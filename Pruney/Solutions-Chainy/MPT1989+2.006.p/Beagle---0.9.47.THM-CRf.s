%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:06 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 420 expanded)
%              Number of leaves         :   33 ( 179 expanded)
%              Depth                    :   13
%              Number of atoms          :  201 (1956 expanded)
%              Number of equality atoms :    6 (  60 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_waybel_6 > v4_waybel_7 > v1_waybel_7 > v1_waybel_0 > v12_waybel_0 > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_lattice3 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_waybel_7,type,(
    v1_waybel_7: ( $i * $i ) > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v5_waybel_6,type,(
    v5_waybel_6: ( $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v12_waybel_0,type,(
    v12_waybel_0: ( $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(v4_waybel_7,type,(
    v4_waybel_7: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(k5_waybel_0,type,(
    k5_waybel_0: ( $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v5_waybel_6(B,A)
             => v4_waybel_7(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_7)).

tff(f_134,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v5_waybel_6(B,A)
           => v1_waybel_7(k5_waybel_0(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_7)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r1_yellow_0(A,k5_waybel_0(A,B))
            & k1_yellow_0(A,k5_waybel_0(A,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => v12_waybel_0(k5_waybel_0(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_waybel_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k5_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v1_xboole_0(k5_waybel_0(A,B))
        & v1_waybel_0(k5_waybel_0(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_waybel_0)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v4_waybel_7(B,A)
          <=> ? [C] :
                ( ~ v1_xboole_0(C)
                & v1_waybel_0(C,A)
                & v12_waybel_0(C,A)
                & v1_waybel_7(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                & B = k1_yellow_0(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_7)).

tff(c_38,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_40,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_48,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_46,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_44,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_42,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_34,plain,(
    v5_waybel_6('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_30,plain,(
    ! [A_21,B_23] :
      ( v1_waybel_7(k5_waybel_0(A_21,B_23),A_21)
      | ~ v5_waybel_6(B_23,A_21)
      | ~ m1_subset_1(B_23,u1_struct_0(A_21))
      | ~ l1_orders_2(A_21)
      | ~ v2_lattice3(A_21)
      | ~ v1_lattice3(A_21)
      | ~ v5_orders_2(A_21)
      | ~ v4_orders_2(A_21)
      | ~ v3_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_62,plain,(
    ! [A_36,B_37] :
      ( k1_yellow_0(A_36,k5_waybel_0(A_36,B_37)) = B_37
      | ~ m1_subset_1(B_37,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36)
      | ~ v5_orders_2(A_36)
      | ~ v4_orders_2(A_36)
      | ~ v3_orders_2(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_64,plain,
    ( k1_yellow_0('#skF_2',k5_waybel_0('#skF_2','#skF_3')) = '#skF_3'
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_62])).

tff(c_67,plain,
    ( k1_yellow_0('#skF_2',k5_waybel_0('#skF_2','#skF_3')) = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_38,c_64])).

tff(c_68,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v2_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_71])).

tff(c_77,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( v12_waybel_0(k5_waybel_0(A_4,B_5),A_4)
      | ~ m1_subset_1(B_5,u1_struct_0(A_4))
      | ~ l1_orders_2(A_4)
      | ~ v4_orders_2(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k5_waybel_0(A_2,B_3),k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ m1_subset_1(B_3,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_waybel_0(k5_waybel_0(A_6,B_7),A_6)
      | ~ m1_subset_1(B_7,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6)
      | ~ v3_orders_2(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_50,plain,(
    ! [A_26,B_27] :
      ( ~ v1_xboole_0(k5_waybel_0(A_26,B_27))
      | ~ m1_subset_1(B_27,u1_struct_0(A_26))
      | ~ l1_orders_2(A_26)
      | ~ v3_orders_2(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_53,plain,
    ( ~ v1_xboole_0(k5_waybel_0('#skF_2','#skF_3'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_50])).

tff(c_56,plain,
    ( ~ v1_xboole_0(k5_waybel_0('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38,c_53])).

tff(c_57,plain,(
    ~ v1_xboole_0(k5_waybel_0('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_32,plain,(
    ~ v4_waybel_7('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_76,plain,(
    k1_yellow_0('#skF_2',k5_waybel_0('#skF_2','#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_100,plain,(
    ! [A_52,C_53] :
      ( v4_waybel_7(k1_yellow_0(A_52,C_53),A_52)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ v1_waybel_7(C_53,A_52)
      | ~ v12_waybel_0(C_53,A_52)
      | ~ v1_waybel_0(C_53,A_52)
      | v1_xboole_0(C_53)
      | ~ m1_subset_1(k1_yellow_0(A_52,C_53),u1_struct_0(A_52))
      | ~ l1_orders_2(A_52)
      | ~ v2_lattice3(A_52)
      | ~ v1_lattice3(A_52)
      | ~ v5_orders_2(A_52)
      | ~ v4_orders_2(A_52)
      | ~ v3_orders_2(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_103,plain,
    ( v4_waybel_7(k1_yellow_0('#skF_2',k5_waybel_0('#skF_2','#skF_3')),'#skF_2')
    | ~ m1_subset_1(k5_waybel_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v1_waybel_7(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v12_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0(k5_waybel_0('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v2_lattice3('#skF_2')
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_100])).

tff(c_105,plain,
    ( v4_waybel_7('#skF_3','#skF_2')
    | ~ m1_subset_1(k5_waybel_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v1_waybel_7(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v12_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0(k5_waybel_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_38,c_36,c_76,c_103])).

tff(c_106,plain,
    ( ~ m1_subset_1(k5_waybel_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v1_waybel_7(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v12_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_32,c_105])).

tff(c_107,plain,(
    ~ v1_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_110,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_107])).

tff(c_113,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38,c_36,c_110])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_113])).

tff(c_116,plain,
    ( ~ v12_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_waybel_7(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1(k5_waybel_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_118,plain,(
    ~ m1_subset_1(k5_waybel_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_121,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_118])).

tff(c_124,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_121])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_124])).

tff(c_127,plain,
    ( ~ v1_waybel_7(k5_waybel_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v12_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_129,plain,(
    ~ v12_waybel_0(k5_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_132,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_129])).

tff(c_135,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_36,c_132])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_135])).

tff(c_138,plain,(
    ~ v1_waybel_7(k5_waybel_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_142,plain,
    ( ~ v5_waybel_6('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v2_lattice3('#skF_2')
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_138])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_38,c_36,c_34,c_142])).

tff(c_147,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_151,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_147,c_2])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:26:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.27  
% 2.20/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.27  %$ v5_waybel_6 > v4_waybel_7 > v1_waybel_7 > v1_waybel_0 > v12_waybel_0 > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_lattice3 > l1_orders_2 > k5_waybel_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.20/1.27  
% 2.20/1.27  %Foreground sorts:
% 2.20/1.27  
% 2.20/1.27  
% 2.20/1.27  %Background operators:
% 2.20/1.27  
% 2.20/1.27  
% 2.20/1.27  %Foreground operators:
% 2.20/1.27  tff(v1_waybel_7, type, v1_waybel_7: ($i * $i) > $o).
% 2.20/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.20/1.27  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 2.20/1.27  tff(v5_waybel_6, type, v5_waybel_6: ($i * $i) > $o).
% 2.20/1.27  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.20/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.27  tff(v12_waybel_0, type, v12_waybel_0: ($i * $i) > $o).
% 2.20/1.27  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.20/1.27  tff(v4_waybel_7, type, v4_waybel_7: ($i * $i) > $o).
% 2.20/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.27  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.20/1.27  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 2.20/1.27  tff(k5_waybel_0, type, k5_waybel_0: ($i * $i) > $i).
% 2.20/1.27  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.20/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.20/1.27  tff(v1_waybel_0, type, v1_waybel_0: ($i * $i) > $o).
% 2.20/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.27  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.20/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.20/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.27  
% 2.20/1.29  tff(f_154, negated_conjecture, ~(![A]: ((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v5_waybel_6(B, A) => v4_waybel_7(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_waybel_7)).
% 2.20/1.29  tff(f_134, axiom, (![A]: ((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v5_waybel_6(B, A) => v1_waybel_7(k5_waybel_0(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_waybel_7)).
% 2.20/1.29  tff(f_84, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r1_yellow_0(A, k5_waybel_0(A, B)) & (k1_yellow_0(A, k5_waybel_0(A, B)) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_waybel_0)).
% 2.20/1.29  tff(f_32, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 2.20/1.29  tff(f_52, axiom, (![A, B]: ((((~v2_struct_0(A) & v4_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => v12_waybel_0(k5_waybel_0(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_waybel_0)).
% 2.20/1.29  tff(f_41, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k5_waybel_0(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_waybel_0)).
% 2.20/1.29  tff(f_66, axiom, (![A, B]: ((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => (~v1_xboole_0(k5_waybel_0(A, B)) & v1_waybel_0(k5_waybel_0(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_waybel_0)).
% 2.20/1.29  tff(f_115, axiom, (![A]: ((((((v3_orders_2(A) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v4_waybel_7(B, A) <=> (?[C]: (((((~v1_xboole_0(C) & v1_waybel_0(C, A)) & v12_waybel_0(C, A)) & v1_waybel_7(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) & (B = k1_yellow_0(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_waybel_7)).
% 2.20/1.29  tff(c_38, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.20/1.29  tff(c_40, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.20/1.29  tff(c_48, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.20/1.29  tff(c_46, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.20/1.29  tff(c_44, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.20/1.29  tff(c_42, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.20/1.29  tff(c_36, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.20/1.29  tff(c_34, plain, (v5_waybel_6('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.20/1.29  tff(c_30, plain, (![A_21, B_23]: (v1_waybel_7(k5_waybel_0(A_21, B_23), A_21) | ~v5_waybel_6(B_23, A_21) | ~m1_subset_1(B_23, u1_struct_0(A_21)) | ~l1_orders_2(A_21) | ~v2_lattice3(A_21) | ~v1_lattice3(A_21) | ~v5_orders_2(A_21) | ~v4_orders_2(A_21) | ~v3_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.20/1.29  tff(c_62, plain, (![A_36, B_37]: (k1_yellow_0(A_36, k5_waybel_0(A_36, B_37))=B_37 | ~m1_subset_1(B_37, u1_struct_0(A_36)) | ~l1_orders_2(A_36) | ~v5_orders_2(A_36) | ~v4_orders_2(A_36) | ~v3_orders_2(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.20/1.29  tff(c_64, plain, (k1_yellow_0('#skF_2', k5_waybel_0('#skF_2', '#skF_3'))='#skF_3' | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_62])).
% 2.20/1.29  tff(c_67, plain, (k1_yellow_0('#skF_2', k5_waybel_0('#skF_2', '#skF_3'))='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_38, c_64])).
% 2.20/1.29  tff(c_68, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_67])).
% 2.20/1.29  tff(c_2, plain, (![A_1]: (~v2_struct_0(A_1) | ~v2_lattice3(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.20/1.29  tff(c_71, plain, (~v2_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_68, c_2])).
% 2.20/1.29  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_71])).
% 2.20/1.29  tff(c_77, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_67])).
% 2.20/1.29  tff(c_6, plain, (![A_4, B_5]: (v12_waybel_0(k5_waybel_0(A_4, B_5), A_4) | ~m1_subset_1(B_5, u1_struct_0(A_4)) | ~l1_orders_2(A_4) | ~v4_orders_2(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.20/1.29  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k5_waybel_0(A_2, B_3), k1_zfmisc_1(u1_struct_0(A_2))) | ~m1_subset_1(B_3, u1_struct_0(A_2)) | ~l1_orders_2(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.20/1.29  tff(c_8, plain, (![A_6, B_7]: (v1_waybel_0(k5_waybel_0(A_6, B_7), A_6) | ~m1_subset_1(B_7, u1_struct_0(A_6)) | ~l1_orders_2(A_6) | ~v3_orders_2(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.20/1.29  tff(c_50, plain, (![A_26, B_27]: (~v1_xboole_0(k5_waybel_0(A_26, B_27)) | ~m1_subset_1(B_27, u1_struct_0(A_26)) | ~l1_orders_2(A_26) | ~v3_orders_2(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.20/1.29  tff(c_53, plain, (~v1_xboole_0(k5_waybel_0('#skF_2', '#skF_3')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_50])).
% 2.20/1.29  tff(c_56, plain, (~v1_xboole_0(k5_waybel_0('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38, c_53])).
% 2.20/1.29  tff(c_57, plain, (~v1_xboole_0(k5_waybel_0('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_56])).
% 2.20/1.29  tff(c_32, plain, (~v4_waybel_7('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.20/1.29  tff(c_76, plain, (k1_yellow_0('#skF_2', k5_waybel_0('#skF_2', '#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_67])).
% 2.20/1.29  tff(c_100, plain, (![A_52, C_53]: (v4_waybel_7(k1_yellow_0(A_52, C_53), A_52) | ~m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~v1_waybel_7(C_53, A_52) | ~v12_waybel_0(C_53, A_52) | ~v1_waybel_0(C_53, A_52) | v1_xboole_0(C_53) | ~m1_subset_1(k1_yellow_0(A_52, C_53), u1_struct_0(A_52)) | ~l1_orders_2(A_52) | ~v2_lattice3(A_52) | ~v1_lattice3(A_52) | ~v5_orders_2(A_52) | ~v4_orders_2(A_52) | ~v3_orders_2(A_52))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.20/1.29  tff(c_103, plain, (v4_waybel_7(k1_yellow_0('#skF_2', k5_waybel_0('#skF_2', '#skF_3')), '#skF_2') | ~m1_subset_1(k5_waybel_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v1_waybel_7(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2') | ~v12_waybel_0(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2') | ~v1_waybel_0(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0(k5_waybel_0('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_76, c_100])).
% 2.20/1.29  tff(c_105, plain, (v4_waybel_7('#skF_3', '#skF_2') | ~m1_subset_1(k5_waybel_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v1_waybel_7(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2') | ~v12_waybel_0(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2') | ~v1_waybel_0(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0(k5_waybel_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_38, c_36, c_76, c_103])).
% 2.20/1.29  tff(c_106, plain, (~m1_subset_1(k5_waybel_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v1_waybel_7(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2') | ~v12_waybel_0(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2') | ~v1_waybel_0(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_57, c_32, c_105])).
% 2.20/1.29  tff(c_107, plain, (~v1_waybel_0(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_106])).
% 2.20/1.29  tff(c_110, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_107])).
% 2.20/1.29  tff(c_113, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38, c_36, c_110])).
% 2.20/1.29  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_113])).
% 2.20/1.29  tff(c_116, plain, (~v12_waybel_0(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2') | ~v1_waybel_7(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1(k5_waybel_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_106])).
% 2.20/1.29  tff(c_118, plain, (~m1_subset_1(k5_waybel_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_116])).
% 2.20/1.29  tff(c_121, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_4, c_118])).
% 2.20/1.29  tff(c_124, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_121])).
% 2.20/1.29  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_124])).
% 2.20/1.29  tff(c_127, plain, (~v1_waybel_7(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2') | ~v12_waybel_0(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_116])).
% 2.20/1.29  tff(c_129, plain, (~v12_waybel_0(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_127])).
% 2.20/1.29  tff(c_132, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_6, c_129])).
% 2.20/1.29  tff(c_135, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_36, c_132])).
% 2.20/1.29  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_135])).
% 2.20/1.29  tff(c_138, plain, (~v1_waybel_7(k5_waybel_0('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_127])).
% 2.20/1.29  tff(c_142, plain, (~v5_waybel_6('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_30, c_138])).
% 2.20/1.29  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_38, c_36, c_34, c_142])).
% 2.20/1.29  tff(c_147, plain, (v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 2.20/1.29  tff(c_151, plain, (~v2_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_147, c_2])).
% 2.20/1.29  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_151])).
% 2.20/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.29  
% 2.20/1.29  Inference rules
% 2.20/1.29  ----------------------
% 2.20/1.29  #Ref     : 0
% 2.20/1.29  #Sup     : 13
% 2.20/1.29  #Fact    : 0
% 2.20/1.29  #Define  : 0
% 2.20/1.29  #Split   : 5
% 2.20/1.29  #Chain   : 0
% 2.20/1.29  #Close   : 0
% 2.20/1.29  
% 2.20/1.29  Ordering : KBO
% 2.20/1.29  
% 2.20/1.29  Simplification rules
% 2.20/1.29  ----------------------
% 2.20/1.29  #Subsume      : 2
% 2.20/1.29  #Demod        : 46
% 2.20/1.29  #Tautology    : 2
% 2.20/1.29  #SimpNegUnit  : 4
% 2.20/1.29  #BackRed      : 0
% 2.20/1.29  
% 2.20/1.29  #Partial instantiations: 0
% 2.20/1.29  #Strategies tried      : 1
% 2.20/1.29  
% 2.20/1.29  Timing (in seconds)
% 2.20/1.29  ----------------------
% 2.20/1.29  Preprocessing        : 0.31
% 2.20/1.29  Parsing              : 0.17
% 2.20/1.29  CNF conversion       : 0.02
% 2.20/1.29  Main loop            : 0.17
% 2.20/1.29  Inferencing          : 0.08
% 2.20/1.29  Reduction            : 0.05
% 2.20/1.29  Demodulation         : 0.04
% 2.20/1.29  BG Simplification    : 0.01
% 2.20/1.29  Subsumption          : 0.02
% 2.20/1.29  Abstraction          : 0.01
% 2.20/1.29  MUC search           : 0.00
% 2.20/1.29  Cooper               : 0.00
% 2.20/1.29  Total                : 0.52
% 2.20/1.29  Index Insertion      : 0.00
% 2.20/1.30  Index Deletion       : 0.00
% 2.20/1.30  Index Matching       : 0.00
% 2.20/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
