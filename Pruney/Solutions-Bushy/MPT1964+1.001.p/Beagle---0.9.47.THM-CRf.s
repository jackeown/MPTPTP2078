%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1964+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:43 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 253 expanded)
%              Number of leaves         :   40 ( 112 expanded)
%              Depth                    :   13
%              Number of atoms          :  237 ( 766 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_yellow_0 > v3_orders_2 > v2_waybel_1 > v2_struct_0 > v2_lattice3 > v1_orders_2 > v1_lattice3 > v11_waybel_1 > v10_waybel_1 > l1_orders_2 > k13_lattice3 > k12_lattice3 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_yellow_1 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v11_waybel_1,type,(
    v11_waybel_1: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v3_yellow_0,type,(
    v3_yellow_0: $i > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(v10_waybel_1,type,(
    v10_waybel_1: $i > $o )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(v2_waybel_1,type,(
    v2_waybel_1: $i > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v13_waybel_0(B,k3_yellow_1(A))
          & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
       => ( v2_waybel_0(B,k3_yellow_1(A))
        <=> ! [C,D] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B) )
             => r2_hidden(k3_xboole_0(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_7)).

tff(f_69,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k3_yellow_1(A))
      & v1_orders_2(k3_yellow_1(A))
      & v3_orders_2(k3_yellow_1(A))
      & v4_orders_2(k3_yellow_1(A))
      & v5_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & l1_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & v11_waybel_1(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_waybel_7)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v11_waybel_1(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & v3_yellow_0(A)
          & v2_waybel_1(A)
          & v10_waybel_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc8_waybel_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r2_hidden(D,B) )
                     => r2_hidden(k12_lattice3(A,C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_waybel_0)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k3_yellow_1(A)))
         => ( k13_lattice3(k3_yellow_1(A),B,C) = k2_xboole_0(B,C)
            & k12_lattice3(k3_yellow_1(A),B,C) = k3_xboole_0(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_1)).

tff(c_64,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | ~ v2_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_84,plain,(
    ~ v2_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_36,plain,(
    ! [A_4] : v5_orders_2(k3_yellow_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_2] : l1_orders_2(k3_yellow_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ! [A_3] : v11_waybel_1(k3_yellow_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_94,plain,(
    ! [A_53] :
      ( v2_lattice3(A_53)
      | ~ v11_waybel_1(A_53)
      | v2_struct_0(A_53)
      | ~ l1_orders_2(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ! [A_4] : ~ v2_struct_0(k3_yellow_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_97,plain,(
    ! [A_4] :
      ( v2_lattice3(k3_yellow_1(A_4))
      | ~ v11_waybel_1(k3_yellow_1(A_4))
      | ~ l1_orders_2(k3_yellow_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_94,c_28])).

tff(c_100,plain,(
    ! [A_4] : v2_lattice3(k3_yellow_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_97])).

tff(c_58,plain,(
    v13_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_157,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_1'(A_81,B_82),B_82)
      | v2_waybel_0(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ v13_waybel_0(B_82,A_81)
      | ~ l1_orders_2(A_81)
      | ~ v2_lattice3(A_81)
      | ~ v5_orders_2(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_159,plain,
    ( r2_hidden('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4')
    | v2_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
    | ~ l1_orders_2(k3_yellow_1('#skF_3'))
    | ~ v2_lattice3(k3_yellow_1('#skF_3'))
    | ~ v5_orders_2(k3_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_157])).

tff(c_162,plain,
    ( r2_hidden('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4')
    | v2_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_100,c_22,c_58,c_159])).

tff(c_163,plain,(
    r2_hidden('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_162])).

tff(c_164,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_2'(A_83,B_84),B_84)
      | v2_waybel_0(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ v13_waybel_0(B_84,A_83)
      | ~ l1_orders_2(A_83)
      | ~ v2_lattice3(A_83)
      | ~ v5_orders_2(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_166,plain,
    ( r2_hidden('#skF_2'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4')
    | v2_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
    | ~ l1_orders_2(k3_yellow_1('#skF_3'))
    | ~ v2_lattice3(k3_yellow_1('#skF_3'))
    | ~ v5_orders_2(k3_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_164])).

tff(c_169,plain,
    ( r2_hidden('#skF_2'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4')
    | v2_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_100,c_22,c_58,c_166])).

tff(c_170,plain,(
    r2_hidden('#skF_2'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_169])).

tff(c_74,plain,(
    ! [C_41,D_42] :
      ( v2_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
      | r2_hidden(k3_xboole_0(C_41,D_42),'#skF_4')
      | ~ r2_hidden(D_42,'#skF_4')
      | ~ r2_hidden(C_41,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_121,plain,(
    ! [C_41,D_42] :
      ( r2_hidden(k3_xboole_0(C_41,D_42),'#skF_4')
      | ~ r2_hidden(D_42,'#skF_4')
      | ~ r2_hidden(C_41,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_74])).

tff(c_171,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1('#skF_1'(A_85,B_86),u1_struct_0(A_85))
      | v2_waybel_0(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ v13_waybel_0(B_86,A_85)
      | ~ l1_orders_2(A_85)
      | ~ v2_lattice3(A_85)
      | ~ v5_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_114,plain,(
    ! [A_61,C_62,B_63] :
      ( m1_subset_1(A_61,C_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(C_62))
      | ~ r2_hidden(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_117,plain,(
    ! [A_61] :
      ( m1_subset_1(A_61,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ r2_hidden(A_61,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_114])).

tff(c_140,plain,(
    ! [A_74,B_75,C_76] :
      ( k12_lattice3(k3_yellow_1(A_74),B_75,C_76) = k3_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,u1_struct_0(k3_yellow_1(A_74)))
      | ~ m1_subset_1(B_75,u1_struct_0(k3_yellow_1(A_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_143,plain,(
    ! [B_75,A_61] :
      ( k12_lattice3(k3_yellow_1('#skF_3'),B_75,A_61) = k3_xboole_0(B_75,A_61)
      | ~ m1_subset_1(B_75,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ r2_hidden(A_61,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_117,c_140])).

tff(c_174,plain,(
    ! [B_86,A_61] :
      ( k12_lattice3(k3_yellow_1('#skF_3'),'#skF_1'(k3_yellow_1('#skF_3'),B_86),A_61) = k3_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),B_86),A_61)
      | ~ r2_hidden(A_61,'#skF_4')
      | v2_waybel_0(B_86,k3_yellow_1('#skF_3'))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_3'))))
      | ~ v13_waybel_0(B_86,k3_yellow_1('#skF_3'))
      | ~ l1_orders_2(k3_yellow_1('#skF_3'))
      | ~ v2_lattice3(k3_yellow_1('#skF_3'))
      | ~ v5_orders_2(k3_yellow_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_171,c_143])).

tff(c_234,plain,(
    ! [B_95,A_96] :
      ( k12_lattice3(k3_yellow_1('#skF_3'),'#skF_1'(k3_yellow_1('#skF_3'),B_95),A_96) = k3_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),B_95),A_96)
      | ~ r2_hidden(A_96,'#skF_4')
      | v2_waybel_0(B_95,k3_yellow_1('#skF_3'))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_3'))))
      | ~ v13_waybel_0(B_95,k3_yellow_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_100,c_22,c_174])).

tff(c_236,plain,(
    ! [A_96] :
      ( k12_lattice3(k3_yellow_1('#skF_3'),'#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),A_96) = k3_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),A_96)
      | ~ r2_hidden(A_96,'#skF_4')
      | v2_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_56,c_234])).

tff(c_239,plain,(
    ! [A_96] :
      ( k12_lattice3(k3_yellow_1('#skF_3'),'#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),A_96) = k3_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),A_96)
      | ~ r2_hidden(A_96,'#skF_4')
      | v2_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_236])).

tff(c_241,plain,(
    ! [A_97] :
      ( k12_lattice3(k3_yellow_1('#skF_3'),'#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),A_97) = k3_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),A_97)
      | ~ r2_hidden(A_97,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_239])).

tff(c_44,plain,(
    ! [A_9,B_23] :
      ( ~ r2_hidden(k12_lattice3(A_9,'#skF_1'(A_9,B_23),'#skF_2'(A_9,B_23)),B_23)
      | v2_waybel_0(B_23,A_9)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ v13_waybel_0(B_23,A_9)
      | ~ l1_orders_2(A_9)
      | ~ v2_lattice3(A_9)
      | ~ v5_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_248,plain,
    ( ~ r2_hidden(k3_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_2'(k3_yellow_1('#skF_3'),'#skF_4')),'#skF_4')
    | v2_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_3'))))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
    | ~ l1_orders_2(k3_yellow_1('#skF_3'))
    | ~ v2_lattice3(k3_yellow_1('#skF_3'))
    | ~ v5_orders_2(k3_yellow_1('#skF_3'))
    | ~ r2_hidden('#skF_2'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_44])).

tff(c_261,plain,
    ( ~ r2_hidden(k3_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_2'(k3_yellow_1('#skF_3'),'#skF_4')),'#skF_4')
    | v2_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_36,c_100,c_22,c_58,c_56,c_248])).

tff(c_262,plain,(
    ~ r2_hidden(k3_xboole_0('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_2'(k3_yellow_1('#skF_3'),'#skF_4')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_261])).

tff(c_272,plain,
    ( ~ r2_hidden('#skF_2'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_1'(k3_yellow_1('#skF_3'),'#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_121,c_262])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_170,c_272])).

tff(c_277,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_278,plain,(
    v2_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ v2_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_279,plain,(
    ~ v2_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_279])).

tff(c_282,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_317,plain,(
    ! [A_109,C_110,B_111] :
      ( m1_subset_1(A_109,C_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(C_110))
      | ~ r2_hidden(A_109,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_320,plain,(
    ! [A_109] :
      ( m1_subset_1(A_109,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ r2_hidden(A_109,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_317])).

tff(c_341,plain,(
    ! [A_120,B_121,C_122] :
      ( k12_lattice3(k3_yellow_1(A_120),B_121,C_122) = k3_xboole_0(B_121,C_122)
      | ~ m1_subset_1(C_122,u1_struct_0(k3_yellow_1(A_120)))
      | ~ m1_subset_1(B_121,u1_struct_0(k3_yellow_1(A_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_345,plain,(
    ! [B_123,A_124] :
      ( k12_lattice3(k3_yellow_1('#skF_3'),B_123,A_124) = k3_xboole_0(B_123,A_124)
      | ~ m1_subset_1(B_123,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ r2_hidden(A_124,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_320,c_341])).

tff(c_348,plain,(
    ! [A_109,A_124] :
      ( k12_lattice3(k3_yellow_1('#skF_3'),A_109,A_124) = k3_xboole_0(A_109,A_124)
      | ~ r2_hidden(A_124,'#skF_4')
      | ~ r2_hidden(A_109,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_320,c_345])).

tff(c_299,plain,(
    ! [A_104] :
      ( v2_lattice3(A_104)
      | ~ v11_waybel_1(A_104)
      | v2_struct_0(A_104)
      | ~ l1_orders_2(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_302,plain,(
    ! [A_4] :
      ( v2_lattice3(k3_yellow_1(A_4))
      | ~ v11_waybel_1(k3_yellow_1(A_4))
      | ~ l1_orders_2(k3_yellow_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_299,c_28])).

tff(c_305,plain,(
    ! [A_4] : v2_lattice3(k3_yellow_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26,c_302])).

tff(c_475,plain,(
    ! [A_157,C_158,D_159,B_160] :
      ( r2_hidden(k12_lattice3(A_157,C_158,D_159),B_160)
      | ~ r2_hidden(D_159,B_160)
      | ~ r2_hidden(C_158,B_160)
      | ~ m1_subset_1(D_159,u1_struct_0(A_157))
      | ~ m1_subset_1(C_158,u1_struct_0(A_157))
      | ~ v2_waybel_0(B_160,A_157)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ v13_waybel_0(B_160,A_157)
      | ~ l1_orders_2(A_157)
      | ~ v2_lattice3(A_157)
      | ~ v5_orders_2(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_477,plain,(
    ! [C_158,D_159] :
      ( r2_hidden(k12_lattice3(k3_yellow_1('#skF_3'),C_158,D_159),'#skF_4')
      | ~ r2_hidden(D_159,'#skF_4')
      | ~ r2_hidden(C_158,'#skF_4')
      | ~ m1_subset_1(D_159,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ m1_subset_1(C_158,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1('#skF_3'))
      | ~ l1_orders_2(k3_yellow_1('#skF_3'))
      | ~ v2_lattice3(k3_yellow_1('#skF_3'))
      | ~ v5_orders_2(k3_yellow_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_56,c_475])).

tff(c_481,plain,(
    ! [C_161,D_162] :
      ( r2_hidden(k12_lattice3(k3_yellow_1('#skF_3'),C_161,D_162),'#skF_4')
      | ~ r2_hidden(D_162,'#skF_4')
      | ~ r2_hidden(C_161,'#skF_4')
      | ~ m1_subset_1(D_162,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ m1_subset_1(C_161,u1_struct_0(k3_yellow_1('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_305,c_22,c_58,c_278,c_477])).

tff(c_492,plain,(
    ! [A_163,A_164] :
      ( r2_hidden(k3_xboole_0(A_163,A_164),'#skF_4')
      | ~ r2_hidden(A_164,'#skF_4')
      | ~ r2_hidden(A_163,'#skF_4')
      | ~ m1_subset_1(A_164,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ m1_subset_1(A_163,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ r2_hidden(A_164,'#skF_4')
      | ~ r2_hidden(A_163,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_481])).

tff(c_508,plain,(
    ! [A_165,A_166] :
      ( r2_hidden(k3_xboole_0(A_165,A_166),'#skF_4')
      | ~ m1_subset_1(A_165,u1_struct_0(k3_yellow_1('#skF_3')))
      | ~ r2_hidden(A_165,'#skF_4')
      | ~ r2_hidden(A_166,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_320,c_492])).

tff(c_524,plain,(
    ! [A_167,A_168] :
      ( r2_hidden(k3_xboole_0(A_167,A_168),'#skF_4')
      | ~ r2_hidden(A_168,'#skF_4')
      | ~ r2_hidden(A_167,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_320,c_508])).

tff(c_60,plain,
    ( ~ r2_hidden(k3_xboole_0('#skF_5','#skF_6'),'#skF_4')
    | ~ v2_waybel_0('#skF_4',k3_yellow_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_294,plain,(
    ~ r2_hidden(k3_xboole_0('#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_60])).

tff(c_527,plain,
    ( ~ r2_hidden('#skF_6','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_524,c_294])).

tff(c_531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_282,c_527])).

%------------------------------------------------------------------------------
