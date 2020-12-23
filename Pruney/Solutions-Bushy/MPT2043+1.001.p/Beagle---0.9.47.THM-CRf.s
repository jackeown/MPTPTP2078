%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2043+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:48 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   65 (  86 expanded)
%              Number of leaves         :   36 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  115 ( 208 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattice3 > v2_struct_0 > v25_waybel_0 > v24_waybel_0 > v1_yellow_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(v3_lattice3,type,(
    v3_lattice3: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v25_waybel_0,type,(
    v25_waybel_0: $i > $o )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v24_waybel_0,type,(
    v24_waybel_0: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k3_yellow_1(A))
      & v1_orders_2(k3_yellow_1(A))
      & v3_orders_2(k3_yellow_1(A))
      & v4_orders_2(k3_yellow_1(A))
      & v5_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
              & v2_waybel_0(B,k3_yellow_1(A))
              & v13_waybel_0(B,k3_yellow_1(A))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
           => ! [C] :
                ~ ( r2_hidden(C,B)
                  & v1_xboole_0(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & l1_orders_2(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_orders_2(k3_yellow_1(A))
      & v3_lattice3(k3_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_yellow_1)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v3_lattice3(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v24_waybel_0(A)
          & v25_waybel_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc11_waybel_0)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v25_waybel_0(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v1_yellow_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc12_waybel_0)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_79,axiom,(
    ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,A)
            & v13_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v1_subset_1(B,u1_struct_0(A))
          <=> ~ r2_hidden(k3_yellow_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

tff(c_20,plain,(
    ! [A_4] : ~ v2_struct_0(k3_yellow_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_24,plain,(
    ! [A_4] : v3_orders_2(k3_yellow_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [A_4] : v4_orders_2(k3_yellow_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_4] : v5_orders_2(k3_yellow_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    ! [A_3] : l1_orders_2(k3_yellow_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [A_5] : v3_lattice3(k3_yellow_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_104,plain,(
    ! [A_30] :
      ( v25_waybel_0(A_30)
      | ~ v3_lattice3(A_30)
      | ~ v3_orders_2(A_30)
      | v2_struct_0(A_30)
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_107,plain,(
    ! [A_4] :
      ( v25_waybel_0(k3_yellow_1(A_4))
      | ~ v3_lattice3(k3_yellow_1(A_4))
      | v2_struct_0(k3_yellow_1(A_4))
      | ~ l1_orders_2(k3_yellow_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_24,c_104])).

tff(c_110,plain,(
    ! [A_4] :
      ( v25_waybel_0(k3_yellow_1(A_4))
      | v2_struct_0(k3_yellow_1(A_4)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32,c_107])).

tff(c_111,plain,(
    ! [A_4] : v25_waybel_0(k3_yellow_1(A_4)) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_110])).

tff(c_113,plain,(
    ! [A_32] :
      ( v1_yellow_0(A_32)
      | ~ v25_waybel_0(A_32)
      | ~ v3_orders_2(A_32)
      | v2_struct_0(A_32)
      | ~ l1_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_116,plain,(
    ! [A_4] :
      ( v1_yellow_0(k3_yellow_1(A_4))
      | ~ v25_waybel_0(k3_yellow_1(A_4))
      | v2_struct_0(k3_yellow_1(A_4))
      | ~ l1_orders_2(k3_yellow_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_24,c_113])).

tff(c_119,plain,(
    ! [A_4] :
      ( v1_yellow_0(k3_yellow_1(A_4))
      | v2_struct_0(k3_yellow_1(A_4)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_111,c_116])).

tff(c_120,plain,(
    ! [A_4] : v1_yellow_0(k3_yellow_1(A_4)) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_119])).

tff(c_52,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_50,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_54,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_46,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_44,plain,(
    v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_75,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_79,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_75])).

tff(c_34,plain,(
    ! [A_6] : k3_yellow_0(k3_yellow_1(A_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_86,plain,(
    ! [A_6] : k3_yellow_0(k3_yellow_1(A_6)) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_34])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_139,plain,(
    ! [A_38,B_39] :
      ( ~ r2_hidden(k3_yellow_0(A_38),B_39)
      | ~ v1_subset_1(B_39,u1_struct_0(A_38))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ v13_waybel_0(B_39,A_38)
      | ~ v2_waybel_0(B_39,A_38)
      | v1_xboole_0(B_39)
      | ~ l1_orders_2(A_38)
      | ~ v1_yellow_0(A_38)
      | ~ v5_orders_2(A_38)
      | ~ v4_orders_2(A_38)
      | ~ v3_orders_2(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_142,plain,
    ( ~ r2_hidden(k3_yellow_0(k3_yellow_1('#skF_1')),'#skF_2')
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1('#skF_1')))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1('#skF_1'))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1('#skF_1'))
    | v1_xboole_0('#skF_2')
    | ~ l1_orders_2(k3_yellow_1('#skF_1'))
    | ~ v1_yellow_0(k3_yellow_1('#skF_1'))
    | ~ v5_orders_2(k3_yellow_1('#skF_1'))
    | ~ v4_orders_2(k3_yellow_1('#skF_1'))
    | ~ v3_orders_2(k3_yellow_1('#skF_1'))
    | v2_struct_0(k3_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_139])).

tff(c_145,plain,
    ( v1_xboole_0('#skF_2')
    | v2_struct_0(k3_yellow_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_28,c_120,c_18,c_52,c_50,c_54,c_46,c_86,c_142])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_56,c_145])).

%------------------------------------------------------------------------------
