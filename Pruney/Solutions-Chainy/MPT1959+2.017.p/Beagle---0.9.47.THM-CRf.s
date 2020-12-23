%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:59 EST 2020

% Result     : Theorem 14.08s
% Output     : CNFRefutation 14.08s
% Verified   : 
% Statistics : Number of formulae       :  165 (1155 expanded)
%              Number of leaves         :   49 ( 411 expanded)
%              Depth                    :   26
%              Number of atoms          :  399 (4038 expanded)
%              Number of equality atoms :   50 ( 360 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_59,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_174,negated_conjecture,(
    ~ ! [A] :
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_145,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,C,D) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

tff(c_6,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_18] : ~ v1_subset_1(k2_subset_1(A_18),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    ! [A_18] : ~ v1_subset_1(A_18,A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_94,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_128,plain,(
    ! [A_80,B_81] :
      ( r2_hidden(A_80,B_81)
      | v1_xboole_0(B_81)
      | ~ m1_subset_1(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_92,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_127,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_131,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_128,c_127])).

tff(c_137,plain,(
    ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_131])).

tff(c_86,plain,
    ( r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
    | ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_139,plain,(
    ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_86])).

tff(c_140,plain,(
    ! [B_82,A_83] :
      ( v1_subset_1(B_82,A_83)
      | B_82 = A_83
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_143,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_66,c_140])).

tff(c_149,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_143])).

tff(c_74,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_112,plain,(
    ! [A_77] :
      ( k1_yellow_0(A_77,k1_xboole_0) = k3_yellow_0(A_77)
      | ~ l1_orders_2(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_116,plain,(
    k1_yellow_0('#skF_6',k1_xboole_0) = k3_yellow_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_112])).

tff(c_121,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1(k1_yellow_0(A_78,B_79),u1_struct_0(A_78))
      | ~ l1_orders_2(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_124,plain,
    ( m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_121])).

tff(c_126,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_124])).

tff(c_162,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_126])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_162])).

tff(c_167,plain,(
    r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_192,plain,(
    ! [C_91,A_92,B_93] :
      ( r2_hidden(C_91,A_92)
      | ~ r2_hidden(C_91,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_202,plain,(
    ! [A_94] :
      ( r2_hidden(k3_yellow_0('#skF_6'),A_94)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_94)) ) ),
    inference(resolution,[status(thm)],[c_167,c_192])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_210,plain,(
    ! [A_95] :
      ( ~ v1_xboole_0(A_95)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_95)) ) ),
    inference(resolution,[status(thm)],[c_202,c_2])).

tff(c_218,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_66,c_210])).

tff(c_628,plain,(
    ! [A_157,B_158,C_159] :
      ( m1_subset_1('#skF_2'(A_157,B_158,C_159),A_157)
      | C_159 = B_158
      | ~ m1_subset_1(C_159,k1_zfmisc_1(A_157))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,(
    ! [A_40,B_42] :
      ( r2_lattice3(A_40,k1_xboole_0,B_42)
      | ~ m1_subset_1(B_42,u1_struct_0(A_40))
      | ~ l1_orders_2(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_666,plain,(
    ! [A_40,B_158,C_159] :
      ( r2_lattice3(A_40,k1_xboole_0,'#skF_2'(u1_struct_0(A_40),B_158,C_159))
      | ~ l1_orders_2(A_40)
      | C_159 = B_158
      | ~ m1_subset_1(C_159,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_40))) ) ),
    inference(resolution,[status(thm)],[c_628,c_48])).

tff(c_1462,plain,(
    ! [A_226,B_227,C_228] :
      ( r2_hidden('#skF_2'(A_226,B_227,C_228),B_227)
      | r2_hidden('#skF_2'(A_226,B_227,C_228),C_228)
      | C_228 = B_227
      | ~ m1_subset_1(C_228,k1_zfmisc_1(A_226))
      | ~ m1_subset_1(B_227,k1_zfmisc_1(A_226)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_277,plain,(
    ! [A_107,C_108,B_109] :
      ( m1_subset_1(A_107,C_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(C_108))
      | ~ r2_hidden(A_107,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_283,plain,(
    ! [A_107,A_6] :
      ( m1_subset_1(A_107,A_6)
      | ~ r2_hidden(A_107,A_6) ) ),
    inference(resolution,[status(thm)],[c_94,c_277])).

tff(c_7869,plain,(
    ! [A_552,B_553,C_554] :
      ( m1_subset_1('#skF_2'(A_552,B_553,C_554),C_554)
      | r2_hidden('#skF_2'(A_552,B_553,C_554),B_553)
      | C_554 = B_553
      | ~ m1_subset_1(C_554,k1_zfmisc_1(A_552))
      | ~ m1_subset_1(B_553,k1_zfmisc_1(A_552)) ) ),
    inference(resolution,[status(thm)],[c_1462,c_283])).

tff(c_8227,plain,(
    ! [A_552,B_553,C_554] :
      ( m1_subset_1('#skF_2'(A_552,B_553,C_554),B_553)
      | m1_subset_1('#skF_2'(A_552,B_553,C_554),C_554)
      | C_554 = B_553
      | ~ m1_subset_1(C_554,k1_zfmisc_1(A_552))
      | ~ m1_subset_1(B_553,k1_zfmisc_1(A_552)) ) ),
    inference(resolution,[status(thm)],[c_7869,c_283])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_481,plain,(
    ! [A_134,A_135,B_136] :
      ( r2_hidden(A_134,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(A_135))
      | v1_xboole_0(B_136)
      | ~ m1_subset_1(A_134,B_136) ) ),
    inference(resolution,[status(thm)],[c_24,c_192])).

tff(c_492,plain,(
    ! [A_134] :
      ( r2_hidden(A_134,u1_struct_0('#skF_6'))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_134,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_481])).

tff(c_502,plain,(
    ! [A_137] :
      ( r2_hidden(A_137,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(A_137,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_492])).

tff(c_514,plain,(
    ! [A_138] :
      ( m1_subset_1(A_138,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(A_138,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_502,c_283])).

tff(c_517,plain,(
    ! [A_138] :
      ( r2_lattice3('#skF_6',k1_xboole_0,A_138)
      | ~ l1_orders_2('#skF_6')
      | ~ m1_subset_1(A_138,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_514,c_48])).

tff(c_523,plain,(
    ! [A_138] :
      ( r2_lattice3('#skF_6',k1_xboole_0,A_138)
      | ~ m1_subset_1(A_138,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_517])).

tff(c_511,plain,(
    ! [A_137] :
      ( m1_subset_1(A_137,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(A_137,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_502,c_283])).

tff(c_68,plain,(
    v13_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_78,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_76,plain,(
    v1_yellow_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_44,plain,(
    ! [A_39] :
      ( r1_yellow_0(A_39,k1_xboole_0)
      | ~ l1_orders_2(A_39)
      | ~ v1_yellow_0(A_39)
      | ~ v5_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2909,plain,(
    ! [A_315,B_316,D_317] :
      ( r1_orders_2(A_315,k1_yellow_0(A_315,B_316),D_317)
      | ~ r2_lattice3(A_315,B_316,D_317)
      | ~ m1_subset_1(D_317,u1_struct_0(A_315))
      | ~ r1_yellow_0(A_315,B_316)
      | ~ m1_subset_1(k1_yellow_0(A_315,B_316),u1_struct_0(A_315))
      | ~ l1_orders_2(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2919,plain,(
    ! [D_317] :
      ( r1_orders_2('#skF_6',k1_yellow_0('#skF_6',k1_xboole_0),D_317)
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_317)
      | ~ m1_subset_1(D_317,u1_struct_0('#skF_6'))
      | ~ r1_yellow_0('#skF_6',k1_xboole_0)
      | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_2909])).

tff(c_2928,plain,(
    ! [D_317] :
      ( r1_orders_2('#skF_6',k3_yellow_0('#skF_6'),D_317)
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_317)
      | ~ m1_subset_1(D_317,u1_struct_0('#skF_6'))
      | ~ r1_yellow_0('#skF_6',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_126,c_116,c_2919])).

tff(c_2929,plain,(
    ~ r1_yellow_0('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2928])).

tff(c_2932,plain,
    ( ~ l1_orders_2('#skF_6')
    | ~ v1_yellow_0('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_2929])).

tff(c_2935,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_2932])).

tff(c_2937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2935])).

tff(c_2938,plain,(
    ! [D_317] :
      ( r1_orders_2('#skF_6',k3_yellow_0('#skF_6'),D_317)
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_317)
      | ~ m1_subset_1(D_317,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_2928])).

tff(c_2973,plain,(
    ! [D_326,B_327,A_328,C_329] :
      ( r2_hidden(D_326,B_327)
      | ~ r1_orders_2(A_328,C_329,D_326)
      | ~ r2_hidden(C_329,B_327)
      | ~ m1_subset_1(D_326,u1_struct_0(A_328))
      | ~ m1_subset_1(C_329,u1_struct_0(A_328))
      | ~ v13_waybel_0(B_327,A_328)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ l1_orders_2(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2977,plain,(
    ! [D_317,B_327] :
      ( r2_hidden(D_317,B_327)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_327)
      | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
      | ~ v13_waybel_0(B_327,'#skF_6')
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_orders_2('#skF_6')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_317)
      | ~ m1_subset_1(D_317,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2938,c_2973])).

tff(c_16152,plain,(
    ! [D_684,B_685] :
      ( r2_hidden(D_684,B_685)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_685)
      | ~ v13_waybel_0(B_685,'#skF_6')
      | ~ m1_subset_1(B_685,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_684)
      | ~ m1_subset_1(D_684,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_126,c_2977])).

tff(c_16247,plain,(
    ! [D_684] :
      ( r2_hidden(D_684,'#skF_7')
      | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_684)
      | ~ m1_subset_1(D_684,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_66,c_16152])).

tff(c_16288,plain,(
    ! [D_686] :
      ( r2_hidden(D_686,'#skF_7')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_686)
      | ~ m1_subset_1(D_686,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_167,c_16247])).

tff(c_16521,plain,(
    ! [A_687] :
      ( r2_hidden(A_687,'#skF_7')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,A_687)
      | ~ m1_subset_1(A_687,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_511,c_16288])).

tff(c_16682,plain,(
    ! [A_688] :
      ( r2_hidden(A_688,'#skF_7')
      | ~ m1_subset_1(A_688,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_523,c_16521])).

tff(c_10,plain,(
    ! [C_10,A_7,B_8] :
      ( r2_hidden(C_10,A_7)
      | ~ r2_hidden(C_10,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5629,plain,(
    ! [A_466,B_467,C_468,A_469] :
      ( r2_hidden('#skF_2'(A_466,B_467,C_468),A_469)
      | ~ m1_subset_1(B_467,k1_zfmisc_1(A_469))
      | r2_hidden('#skF_2'(A_466,B_467,C_468),C_468)
      | C_468 = B_467
      | ~ m1_subset_1(C_468,k1_zfmisc_1(A_466))
      | ~ m1_subset_1(B_467,k1_zfmisc_1(A_466)) ) ),
    inference(resolution,[status(thm)],[c_1462,c_10])).

tff(c_5724,plain,(
    ! [A_466,B_467,C_468,A_469] :
      ( m1_subset_1('#skF_2'(A_466,B_467,C_468),A_469)
      | ~ m1_subset_1(B_467,k1_zfmisc_1(A_469))
      | r2_hidden('#skF_2'(A_466,B_467,C_468),C_468)
      | C_468 = B_467
      | ~ m1_subset_1(C_468,k1_zfmisc_1(A_466))
      | ~ m1_subset_1(B_467,k1_zfmisc_1(A_466)) ) ),
    inference(resolution,[status(thm)],[c_5629,c_283])).

tff(c_12,plain,(
    ! [A_11,B_12,C_16] :
      ( m1_subset_1('#skF_2'(A_11,B_12,C_16),A_11)
      | C_16 = B_12
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1712,plain,(
    ! [A_242,B_243,C_244] :
      ( ~ r2_hidden('#skF_2'(A_242,B_243,C_244),C_244)
      | ~ r2_hidden('#skF_2'(A_242,B_243,C_244),B_243)
      | C_244 = B_243
      | ~ m1_subset_1(C_244,k1_zfmisc_1(A_242))
      | ~ m1_subset_1(B_243,k1_zfmisc_1(A_242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4117,plain,(
    ! [A_386,B_387,B_388] :
      ( ~ r2_hidden('#skF_2'(A_386,B_387,B_388),B_387)
      | B_388 = B_387
      | ~ m1_subset_1(B_388,k1_zfmisc_1(A_386))
      | ~ m1_subset_1(B_387,k1_zfmisc_1(A_386))
      | v1_xboole_0(B_388)
      | ~ m1_subset_1('#skF_2'(A_386,B_387,B_388),B_388) ) ),
    inference(resolution,[status(thm)],[c_24,c_1712])).

tff(c_13680,plain,(
    ! [B_647,B_646,A_648] :
      ( B_647 = B_646
      | ~ m1_subset_1(B_646,k1_zfmisc_1(A_648))
      | ~ m1_subset_1(B_647,k1_zfmisc_1(A_648))
      | v1_xboole_0(B_646)
      | ~ m1_subset_1('#skF_2'(A_648,B_647,B_646),B_646)
      | v1_xboole_0(B_647)
      | ~ m1_subset_1('#skF_2'(A_648,B_647,B_646),B_647) ) ),
    inference(resolution,[status(thm)],[c_24,c_4117])).

tff(c_13711,plain,(
    ! [A_11,B_12] :
      ( v1_xboole_0(A_11)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1('#skF_2'(A_11,B_12,A_11),B_12)
      | B_12 = A_11
      | ~ m1_subset_1(A_11,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_12,c_13680])).

tff(c_13744,plain,(
    ! [A_649,B_650] :
      ( v1_xboole_0(A_649)
      | v1_xboole_0(B_650)
      | ~ m1_subset_1('#skF_2'(A_649,B_650,A_649),B_650)
      | B_650 = A_649
      | ~ m1_subset_1(B_650,k1_zfmisc_1(A_649)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_13711])).

tff(c_13758,plain,(
    ! [C_468,A_469] :
      ( v1_xboole_0(C_468)
      | v1_xboole_0(A_469)
      | ~ m1_subset_1(A_469,k1_zfmisc_1(A_469))
      | r2_hidden('#skF_2'(C_468,A_469,C_468),C_468)
      | C_468 = A_469
      | ~ m1_subset_1(C_468,k1_zfmisc_1(C_468))
      | ~ m1_subset_1(A_469,k1_zfmisc_1(C_468)) ) ),
    inference(resolution,[status(thm)],[c_5724,c_13744])).

tff(c_13845,plain,(
    ! [C_651,A_652] :
      ( v1_xboole_0(C_651)
      | v1_xboole_0(A_652)
      | r2_hidden('#skF_2'(C_651,A_652,C_651),C_651)
      | C_651 = A_652
      | ~ m1_subset_1(A_652,k1_zfmisc_1(C_651)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_13758])).

tff(c_14,plain,(
    ! [A_11,B_12,C_16] :
      ( ~ r2_hidden('#skF_2'(A_11,B_12,C_16),C_16)
      | ~ r2_hidden('#skF_2'(A_11,B_12,C_16),B_12)
      | C_16 = B_12
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_13879,plain,(
    ! [C_651,A_652] :
      ( ~ r2_hidden('#skF_2'(C_651,A_652,C_651),A_652)
      | ~ m1_subset_1(C_651,k1_zfmisc_1(C_651))
      | v1_xboole_0(C_651)
      | v1_xboole_0(A_652)
      | C_651 = A_652
      | ~ m1_subset_1(A_652,k1_zfmisc_1(C_651)) ) ),
    inference(resolution,[status(thm)],[c_13845,c_14])).

tff(c_13922,plain,(
    ! [C_651,A_652] :
      ( ~ r2_hidden('#skF_2'(C_651,A_652,C_651),A_652)
      | v1_xboole_0(C_651)
      | v1_xboole_0(A_652)
      | C_651 = A_652
      | ~ m1_subset_1(A_652,k1_zfmisc_1(C_651)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_13879])).

tff(c_16689,plain,(
    ! [C_651] :
      ( v1_xboole_0(C_651)
      | v1_xboole_0('#skF_7')
      | C_651 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(C_651))
      | ~ m1_subset_1('#skF_2'(C_651,'#skF_7',C_651),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_16682,c_13922])).

tff(c_17290,plain,(
    ! [C_695] :
      ( v1_xboole_0(C_695)
      | C_695 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(C_695))
      | ~ m1_subset_1('#skF_2'(C_695,'#skF_7',C_695),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_16689])).

tff(c_17318,plain,(
    ! [C_554] :
      ( v1_xboole_0(C_554)
      | m1_subset_1('#skF_2'(C_554,'#skF_7',C_554),C_554)
      | C_554 = '#skF_7'
      | ~ m1_subset_1(C_554,k1_zfmisc_1(C_554))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(C_554)) ) ),
    inference(resolution,[status(thm)],[c_8227,c_17290])).

tff(c_21458,plain,(
    ! [C_790] :
      ( v1_xboole_0(C_790)
      | m1_subset_1('#skF_2'(C_790,'#skF_7',C_790),C_790)
      | C_790 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(C_790)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_17318])).

tff(c_16284,plain,(
    ! [D_684] :
      ( r2_hidden(D_684,'#skF_7')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_684)
      | ~ m1_subset_1(D_684,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_167,c_16247])).

tff(c_21487,plain,
    ( r2_hidden('#skF_2'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')),'#skF_7')
    | ~ r2_lattice3('#skF_6',k1_xboole_0,'#skF_2'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')))
    | v1_xboole_0(u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_21458,c_16284])).

tff(c_21788,plain,
    ( r2_hidden('#skF_2'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')),'#skF_7')
    | ~ r2_lattice3('#skF_6',k1_xboole_0,'#skF_2'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')))
    | v1_xboole_0(u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_21487])).

tff(c_21789,plain,
    ( r2_hidden('#skF_2'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')),'#skF_7')
    | ~ r2_lattice3('#skF_6',k1_xboole_0,'#skF_2'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_21788])).

tff(c_21937,plain,(
    ~ r2_lattice3('#skF_6',k1_xboole_0,'#skF_2'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_21789])).

tff(c_21940,plain,
    ( ~ l1_orders_2('#skF_6')
    | u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_666,c_21937])).

tff(c_21949,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_94,c_74,c_21940])).

tff(c_500,plain,(
    ! [A_134] :
      ( r2_hidden(A_134,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(A_134,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_492])).

tff(c_4190,plain,(
    ! [B_393,A_394] :
      ( u1_struct_0('#skF_6') = B_393
      | ~ m1_subset_1(B_393,k1_zfmisc_1(A_394))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_394))
      | v1_xboole_0(B_393)
      | ~ m1_subset_1('#skF_2'(A_394,u1_struct_0('#skF_6'),B_393),B_393)
      | ~ m1_subset_1('#skF_2'(A_394,u1_struct_0('#skF_6'),B_393),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_500,c_4117])).

tff(c_4199,plain,(
    ! [A_11] :
      ( v1_xboole_0(A_11)
      | ~ m1_subset_1('#skF_2'(A_11,u1_struct_0('#skF_6'),A_11),'#skF_7')
      | u1_struct_0('#skF_6') = A_11
      | ~ m1_subset_1(A_11,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_12,c_4190])).

tff(c_4220,plain,(
    ! [A_395] :
      ( v1_xboole_0(A_395)
      | ~ m1_subset_1('#skF_2'(A_395,u1_struct_0('#skF_6'),A_395),'#skF_7')
      | u1_struct_0('#skF_6') = A_395
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_395)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_4199])).

tff(c_4228,plain,
    ( v1_xboole_0('#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_12,c_4220])).

tff(c_4235,plain,
    ( v1_xboole_0('#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_4228])).

tff(c_4236,plain,
    ( u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4235])).

tff(c_4237,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_4236])).

tff(c_22004,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21949,c_4237])).

tff(c_22043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_22004])).

tff(c_22044,plain,
    ( u1_struct_0('#skF_6') = '#skF_7'
    | r2_hidden('#skF_2'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_21789])).

tff(c_22053,plain,(
    r2_hidden('#skF_2'(u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_6')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_22044])).

tff(c_22056,plain,
    ( v1_xboole_0(u1_struct_0('#skF_6'))
    | v1_xboole_0('#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_22053,c_13922])).

tff(c_22078,plain,
    ( v1_xboole_0(u1_struct_0('#skF_6'))
    | v1_xboole_0('#skF_7')
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_22056])).

tff(c_22079,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_218,c_22078])).

tff(c_22150,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22079,c_4237])).

tff(c_22189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_22150])).

tff(c_22190,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_22044])).

tff(c_22244,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22190,c_4237])).

tff(c_22283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_22244])).

tff(c_22284,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_4236])).

tff(c_166,plain,(
    v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_22310,plain,(
    v1_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22284,c_166])).

tff(c_22315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_22310])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 10:12:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.08/6.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.08/6.71  
% 14.08/6.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.08/6.72  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4
% 14.08/6.72  
% 14.08/6.72  %Foreground sorts:
% 14.08/6.72  
% 14.08/6.72  
% 14.08/6.72  %Background operators:
% 14.08/6.72  
% 14.08/6.72  
% 14.08/6.72  %Foreground operators:
% 14.08/6.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.08/6.72  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 14.08/6.72  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 14.08/6.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.08/6.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.08/6.72  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 14.08/6.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.08/6.72  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 14.08/6.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.08/6.72  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 14.08/6.72  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 14.08/6.72  tff('#skF_7', type, '#skF_7': $i).
% 14.08/6.72  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 14.08/6.72  tff('#skF_6', type, '#skF_6': $i).
% 14.08/6.72  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 14.08/6.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.08/6.72  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 14.08/6.72  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 14.08/6.72  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 14.08/6.72  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 14.08/6.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.08/6.72  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 14.08/6.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.08/6.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.08/6.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.08/6.72  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 14.08/6.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.08/6.72  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.08/6.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.08/6.72  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 14.08/6.72  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 14.08/6.72  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 14.08/6.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.08/6.72  
% 14.08/6.74  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 14.08/6.74  tff(f_59, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 14.08/6.74  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 14.08/6.74  tff(f_174, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 14.08/6.74  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 14.08/6.74  tff(f_145, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 14.08/6.74  tff(f_75, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 14.08/6.74  tff(f_97, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 14.08/6.74  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 14.08/6.74  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 14.08/6.74  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 14.08/6.74  tff(f_119, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 14.08/6.74  tff(f_71, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 14.08/6.74  tff(f_110, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_0)).
% 14.08/6.74  tff(f_93, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 14.08/6.74  tff(f_138, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 14.08/6.74  tff(c_6, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.08/6.74  tff(c_22, plain, (![A_18]: (~v1_subset_1(k2_subset_1(A_18), A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.08/6.74  tff(c_93, plain, (![A_18]: (~v1_subset_1(A_18, A_18))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22])).
% 14.08/6.74  tff(c_8, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.08/6.74  tff(c_94, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 14.08/6.74  tff(c_72, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.08/6.74  tff(c_66, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.08/6.74  tff(c_128, plain, (![A_80, B_81]: (r2_hidden(A_80, B_81) | v1_xboole_0(B_81) | ~m1_subset_1(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.08/6.74  tff(c_92, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.08/6.74  tff(c_127, plain, (~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_92])).
% 14.08/6.74  tff(c_131, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_128, c_127])).
% 14.08/6.74  tff(c_137, plain, (~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_72, c_131])).
% 14.08/6.74  tff(c_86, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.08/6.74  tff(c_139, plain, (~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_127, c_86])).
% 14.08/6.74  tff(c_140, plain, (![B_82, A_83]: (v1_subset_1(B_82, A_83) | B_82=A_83 | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_145])).
% 14.08/6.74  tff(c_143, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_66, c_140])).
% 14.08/6.74  tff(c_149, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_139, c_143])).
% 14.08/6.74  tff(c_74, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.08/6.74  tff(c_112, plain, (![A_77]: (k1_yellow_0(A_77, k1_xboole_0)=k3_yellow_0(A_77) | ~l1_orders_2(A_77))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.08/6.74  tff(c_116, plain, (k1_yellow_0('#skF_6', k1_xboole_0)=k3_yellow_0('#skF_6')), inference(resolution, [status(thm)], [c_74, c_112])).
% 14.08/6.74  tff(c_121, plain, (![A_78, B_79]: (m1_subset_1(k1_yellow_0(A_78, B_79), u1_struct_0(A_78)) | ~l1_orders_2(A_78))), inference(cnfTransformation, [status(thm)], [f_97])).
% 14.08/6.74  tff(c_124, plain, (m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_116, c_121])).
% 14.08/6.74  tff(c_126, plain, (m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_124])).
% 14.08/6.74  tff(c_162, plain, (m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_126])).
% 14.08/6.74  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_162])).
% 14.08/6.74  tff(c_167, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_92])).
% 14.08/6.74  tff(c_192, plain, (![C_91, A_92, B_93]: (r2_hidden(C_91, A_92) | ~r2_hidden(C_91, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.08/6.74  tff(c_202, plain, (![A_94]: (r2_hidden(k3_yellow_0('#skF_6'), A_94) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_94)))), inference(resolution, [status(thm)], [c_167, c_192])).
% 14.08/6.74  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.08/6.74  tff(c_210, plain, (![A_95]: (~v1_xboole_0(A_95) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_95)))), inference(resolution, [status(thm)], [c_202, c_2])).
% 14.08/6.74  tff(c_218, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_210])).
% 14.08/6.74  tff(c_628, plain, (![A_157, B_158, C_159]: (m1_subset_1('#skF_2'(A_157, B_158, C_159), A_157) | C_159=B_158 | ~m1_subset_1(C_159, k1_zfmisc_1(A_157)) | ~m1_subset_1(B_158, k1_zfmisc_1(A_157)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.08/6.74  tff(c_48, plain, (![A_40, B_42]: (r2_lattice3(A_40, k1_xboole_0, B_42) | ~m1_subset_1(B_42, u1_struct_0(A_40)) | ~l1_orders_2(A_40))), inference(cnfTransformation, [status(thm)], [f_119])).
% 14.08/6.74  tff(c_666, plain, (![A_40, B_158, C_159]: (r2_lattice3(A_40, k1_xboole_0, '#skF_2'(u1_struct_0(A_40), B_158, C_159)) | ~l1_orders_2(A_40) | C_159=B_158 | ~m1_subset_1(C_159, k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_40))))), inference(resolution, [status(thm)], [c_628, c_48])).
% 14.08/6.74  tff(c_1462, plain, (![A_226, B_227, C_228]: (r2_hidden('#skF_2'(A_226, B_227, C_228), B_227) | r2_hidden('#skF_2'(A_226, B_227, C_228), C_228) | C_228=B_227 | ~m1_subset_1(C_228, k1_zfmisc_1(A_226)) | ~m1_subset_1(B_227, k1_zfmisc_1(A_226)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.08/6.74  tff(c_277, plain, (![A_107, C_108, B_109]: (m1_subset_1(A_107, C_108) | ~m1_subset_1(B_109, k1_zfmisc_1(C_108)) | ~r2_hidden(A_107, B_109))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.08/6.74  tff(c_283, plain, (![A_107, A_6]: (m1_subset_1(A_107, A_6) | ~r2_hidden(A_107, A_6))), inference(resolution, [status(thm)], [c_94, c_277])).
% 14.08/6.74  tff(c_7869, plain, (![A_552, B_553, C_554]: (m1_subset_1('#skF_2'(A_552, B_553, C_554), C_554) | r2_hidden('#skF_2'(A_552, B_553, C_554), B_553) | C_554=B_553 | ~m1_subset_1(C_554, k1_zfmisc_1(A_552)) | ~m1_subset_1(B_553, k1_zfmisc_1(A_552)))), inference(resolution, [status(thm)], [c_1462, c_283])).
% 14.08/6.74  tff(c_8227, plain, (![A_552, B_553, C_554]: (m1_subset_1('#skF_2'(A_552, B_553, C_554), B_553) | m1_subset_1('#skF_2'(A_552, B_553, C_554), C_554) | C_554=B_553 | ~m1_subset_1(C_554, k1_zfmisc_1(A_552)) | ~m1_subset_1(B_553, k1_zfmisc_1(A_552)))), inference(resolution, [status(thm)], [c_7869, c_283])).
% 14.08/6.74  tff(c_24, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.08/6.74  tff(c_481, plain, (![A_134, A_135, B_136]: (r2_hidden(A_134, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(A_135)) | v1_xboole_0(B_136) | ~m1_subset_1(A_134, B_136))), inference(resolution, [status(thm)], [c_24, c_192])).
% 14.08/6.74  tff(c_492, plain, (![A_134]: (r2_hidden(A_134, u1_struct_0('#skF_6')) | v1_xboole_0('#skF_7') | ~m1_subset_1(A_134, '#skF_7'))), inference(resolution, [status(thm)], [c_66, c_481])).
% 14.08/6.74  tff(c_502, plain, (![A_137]: (r2_hidden(A_137, u1_struct_0('#skF_6')) | ~m1_subset_1(A_137, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_492])).
% 14.08/6.74  tff(c_514, plain, (![A_138]: (m1_subset_1(A_138, u1_struct_0('#skF_6')) | ~m1_subset_1(A_138, '#skF_7'))), inference(resolution, [status(thm)], [c_502, c_283])).
% 14.08/6.74  tff(c_517, plain, (![A_138]: (r2_lattice3('#skF_6', k1_xboole_0, A_138) | ~l1_orders_2('#skF_6') | ~m1_subset_1(A_138, '#skF_7'))), inference(resolution, [status(thm)], [c_514, c_48])).
% 14.08/6.74  tff(c_523, plain, (![A_138]: (r2_lattice3('#skF_6', k1_xboole_0, A_138) | ~m1_subset_1(A_138, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_517])).
% 14.08/6.74  tff(c_511, plain, (![A_137]: (m1_subset_1(A_137, u1_struct_0('#skF_6')) | ~m1_subset_1(A_137, '#skF_7'))), inference(resolution, [status(thm)], [c_502, c_283])).
% 14.08/6.74  tff(c_68, plain, (v13_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.08/6.74  tff(c_84, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.08/6.74  tff(c_78, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.08/6.74  tff(c_76, plain, (v1_yellow_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.08/6.74  tff(c_44, plain, (![A_39]: (r1_yellow_0(A_39, k1_xboole_0) | ~l1_orders_2(A_39) | ~v1_yellow_0(A_39) | ~v5_orders_2(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.08/6.74  tff(c_2909, plain, (![A_315, B_316, D_317]: (r1_orders_2(A_315, k1_yellow_0(A_315, B_316), D_317) | ~r2_lattice3(A_315, B_316, D_317) | ~m1_subset_1(D_317, u1_struct_0(A_315)) | ~r1_yellow_0(A_315, B_316) | ~m1_subset_1(k1_yellow_0(A_315, B_316), u1_struct_0(A_315)) | ~l1_orders_2(A_315))), inference(cnfTransformation, [status(thm)], [f_93])).
% 14.08/6.74  tff(c_2919, plain, (![D_317]: (r1_orders_2('#skF_6', k1_yellow_0('#skF_6', k1_xboole_0), D_317) | ~r2_lattice3('#skF_6', k1_xboole_0, D_317) | ~m1_subset_1(D_317, u1_struct_0('#skF_6')) | ~r1_yellow_0('#skF_6', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_2909])).
% 14.08/6.74  tff(c_2928, plain, (![D_317]: (r1_orders_2('#skF_6', k3_yellow_0('#skF_6'), D_317) | ~r2_lattice3('#skF_6', k1_xboole_0, D_317) | ~m1_subset_1(D_317, u1_struct_0('#skF_6')) | ~r1_yellow_0('#skF_6', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_126, c_116, c_2919])).
% 14.08/6.74  tff(c_2929, plain, (~r1_yellow_0('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2928])).
% 14.08/6.74  tff(c_2932, plain, (~l1_orders_2('#skF_6') | ~v1_yellow_0('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_44, c_2929])).
% 14.08/6.74  tff(c_2935, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_2932])).
% 14.08/6.74  tff(c_2937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_2935])).
% 14.08/6.74  tff(c_2938, plain, (![D_317]: (r1_orders_2('#skF_6', k3_yellow_0('#skF_6'), D_317) | ~r2_lattice3('#skF_6', k1_xboole_0, D_317) | ~m1_subset_1(D_317, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_2928])).
% 14.08/6.74  tff(c_2973, plain, (![D_326, B_327, A_328, C_329]: (r2_hidden(D_326, B_327) | ~r1_orders_2(A_328, C_329, D_326) | ~r2_hidden(C_329, B_327) | ~m1_subset_1(D_326, u1_struct_0(A_328)) | ~m1_subset_1(C_329, u1_struct_0(A_328)) | ~v13_waybel_0(B_327, A_328) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(A_328))) | ~l1_orders_2(A_328))), inference(cnfTransformation, [status(thm)], [f_138])).
% 14.08/6.74  tff(c_2977, plain, (![D_317, B_327]: (r2_hidden(D_317, B_327) | ~r2_hidden(k3_yellow_0('#skF_6'), B_327) | ~m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~v13_waybel_0(B_327, '#skF_6') | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~r2_lattice3('#skF_6', k1_xboole_0, D_317) | ~m1_subset_1(D_317, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_2938, c_2973])).
% 14.08/6.74  tff(c_16152, plain, (![D_684, B_685]: (r2_hidden(D_684, B_685) | ~r2_hidden(k3_yellow_0('#skF_6'), B_685) | ~v13_waybel_0(B_685, '#skF_6') | ~m1_subset_1(B_685, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_lattice3('#skF_6', k1_xboole_0, D_684) | ~m1_subset_1(D_684, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_126, c_2977])).
% 14.08/6.74  tff(c_16247, plain, (![D_684]: (r2_hidden(D_684, '#skF_7') | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v13_waybel_0('#skF_7', '#skF_6') | ~r2_lattice3('#skF_6', k1_xboole_0, D_684) | ~m1_subset_1(D_684, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_66, c_16152])).
% 14.08/6.74  tff(c_16288, plain, (![D_686]: (r2_hidden(D_686, '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, D_686) | ~m1_subset_1(D_686, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_167, c_16247])).
% 14.08/6.74  tff(c_16521, plain, (![A_687]: (r2_hidden(A_687, '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, A_687) | ~m1_subset_1(A_687, '#skF_7'))), inference(resolution, [status(thm)], [c_511, c_16288])).
% 14.08/6.74  tff(c_16682, plain, (![A_688]: (r2_hidden(A_688, '#skF_7') | ~m1_subset_1(A_688, '#skF_7'))), inference(resolution, [status(thm)], [c_523, c_16521])).
% 14.08/6.74  tff(c_10, plain, (![C_10, A_7, B_8]: (r2_hidden(C_10, A_7) | ~r2_hidden(C_10, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.08/6.74  tff(c_5629, plain, (![A_466, B_467, C_468, A_469]: (r2_hidden('#skF_2'(A_466, B_467, C_468), A_469) | ~m1_subset_1(B_467, k1_zfmisc_1(A_469)) | r2_hidden('#skF_2'(A_466, B_467, C_468), C_468) | C_468=B_467 | ~m1_subset_1(C_468, k1_zfmisc_1(A_466)) | ~m1_subset_1(B_467, k1_zfmisc_1(A_466)))), inference(resolution, [status(thm)], [c_1462, c_10])).
% 14.08/6.74  tff(c_5724, plain, (![A_466, B_467, C_468, A_469]: (m1_subset_1('#skF_2'(A_466, B_467, C_468), A_469) | ~m1_subset_1(B_467, k1_zfmisc_1(A_469)) | r2_hidden('#skF_2'(A_466, B_467, C_468), C_468) | C_468=B_467 | ~m1_subset_1(C_468, k1_zfmisc_1(A_466)) | ~m1_subset_1(B_467, k1_zfmisc_1(A_466)))), inference(resolution, [status(thm)], [c_5629, c_283])).
% 14.08/6.74  tff(c_12, plain, (![A_11, B_12, C_16]: (m1_subset_1('#skF_2'(A_11, B_12, C_16), A_11) | C_16=B_12 | ~m1_subset_1(C_16, k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.08/6.74  tff(c_1712, plain, (![A_242, B_243, C_244]: (~r2_hidden('#skF_2'(A_242, B_243, C_244), C_244) | ~r2_hidden('#skF_2'(A_242, B_243, C_244), B_243) | C_244=B_243 | ~m1_subset_1(C_244, k1_zfmisc_1(A_242)) | ~m1_subset_1(B_243, k1_zfmisc_1(A_242)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.08/6.74  tff(c_4117, plain, (![A_386, B_387, B_388]: (~r2_hidden('#skF_2'(A_386, B_387, B_388), B_387) | B_388=B_387 | ~m1_subset_1(B_388, k1_zfmisc_1(A_386)) | ~m1_subset_1(B_387, k1_zfmisc_1(A_386)) | v1_xboole_0(B_388) | ~m1_subset_1('#skF_2'(A_386, B_387, B_388), B_388))), inference(resolution, [status(thm)], [c_24, c_1712])).
% 14.08/6.74  tff(c_13680, plain, (![B_647, B_646, A_648]: (B_647=B_646 | ~m1_subset_1(B_646, k1_zfmisc_1(A_648)) | ~m1_subset_1(B_647, k1_zfmisc_1(A_648)) | v1_xboole_0(B_646) | ~m1_subset_1('#skF_2'(A_648, B_647, B_646), B_646) | v1_xboole_0(B_647) | ~m1_subset_1('#skF_2'(A_648, B_647, B_646), B_647))), inference(resolution, [status(thm)], [c_24, c_4117])).
% 14.08/6.74  tff(c_13711, plain, (![A_11, B_12]: (v1_xboole_0(A_11) | v1_xboole_0(B_12) | ~m1_subset_1('#skF_2'(A_11, B_12, A_11), B_12) | B_12=A_11 | ~m1_subset_1(A_11, k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_12, c_13680])).
% 14.08/6.74  tff(c_13744, plain, (![A_649, B_650]: (v1_xboole_0(A_649) | v1_xboole_0(B_650) | ~m1_subset_1('#skF_2'(A_649, B_650, A_649), B_650) | B_650=A_649 | ~m1_subset_1(B_650, k1_zfmisc_1(A_649)))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_13711])).
% 14.08/6.74  tff(c_13758, plain, (![C_468, A_469]: (v1_xboole_0(C_468) | v1_xboole_0(A_469) | ~m1_subset_1(A_469, k1_zfmisc_1(A_469)) | r2_hidden('#skF_2'(C_468, A_469, C_468), C_468) | C_468=A_469 | ~m1_subset_1(C_468, k1_zfmisc_1(C_468)) | ~m1_subset_1(A_469, k1_zfmisc_1(C_468)))), inference(resolution, [status(thm)], [c_5724, c_13744])).
% 14.08/6.74  tff(c_13845, plain, (![C_651, A_652]: (v1_xboole_0(C_651) | v1_xboole_0(A_652) | r2_hidden('#skF_2'(C_651, A_652, C_651), C_651) | C_651=A_652 | ~m1_subset_1(A_652, k1_zfmisc_1(C_651)))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_13758])).
% 14.08/6.74  tff(c_14, plain, (![A_11, B_12, C_16]: (~r2_hidden('#skF_2'(A_11, B_12, C_16), C_16) | ~r2_hidden('#skF_2'(A_11, B_12, C_16), B_12) | C_16=B_12 | ~m1_subset_1(C_16, k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.08/6.74  tff(c_13879, plain, (![C_651, A_652]: (~r2_hidden('#skF_2'(C_651, A_652, C_651), A_652) | ~m1_subset_1(C_651, k1_zfmisc_1(C_651)) | v1_xboole_0(C_651) | v1_xboole_0(A_652) | C_651=A_652 | ~m1_subset_1(A_652, k1_zfmisc_1(C_651)))), inference(resolution, [status(thm)], [c_13845, c_14])).
% 14.08/6.74  tff(c_13922, plain, (![C_651, A_652]: (~r2_hidden('#skF_2'(C_651, A_652, C_651), A_652) | v1_xboole_0(C_651) | v1_xboole_0(A_652) | C_651=A_652 | ~m1_subset_1(A_652, k1_zfmisc_1(C_651)))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_13879])).
% 14.08/6.74  tff(c_16689, plain, (![C_651]: (v1_xboole_0(C_651) | v1_xboole_0('#skF_7') | C_651='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(C_651)) | ~m1_subset_1('#skF_2'(C_651, '#skF_7', C_651), '#skF_7'))), inference(resolution, [status(thm)], [c_16682, c_13922])).
% 14.08/6.74  tff(c_17290, plain, (![C_695]: (v1_xboole_0(C_695) | C_695='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(C_695)) | ~m1_subset_1('#skF_2'(C_695, '#skF_7', C_695), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_16689])).
% 14.08/6.74  tff(c_17318, plain, (![C_554]: (v1_xboole_0(C_554) | m1_subset_1('#skF_2'(C_554, '#skF_7', C_554), C_554) | C_554='#skF_7' | ~m1_subset_1(C_554, k1_zfmisc_1(C_554)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(C_554)))), inference(resolution, [status(thm)], [c_8227, c_17290])).
% 14.08/6.74  tff(c_21458, plain, (![C_790]: (v1_xboole_0(C_790) | m1_subset_1('#skF_2'(C_790, '#skF_7', C_790), C_790) | C_790='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(C_790)))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_17318])).
% 14.08/6.74  tff(c_16284, plain, (![D_684]: (r2_hidden(D_684, '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, D_684) | ~m1_subset_1(D_684, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_167, c_16247])).
% 14.08/6.74  tff(c_21487, plain, (r2_hidden('#skF_2'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6')), '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, '#skF_2'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6'))) | v1_xboole_0(u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_21458, c_16284])).
% 14.08/6.74  tff(c_21788, plain, (r2_hidden('#skF_2'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6')), '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, '#skF_2'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6'))) | v1_xboole_0(u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_21487])).
% 14.08/6.74  tff(c_21789, plain, (r2_hidden('#skF_2'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6')), '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, '#skF_2'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6'))) | u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_218, c_21788])).
% 14.08/6.74  tff(c_21937, plain, (~r2_lattice3('#skF_6', k1_xboole_0, '#skF_2'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6')))), inference(splitLeft, [status(thm)], [c_21789])).
% 14.08/6.74  tff(c_21940, plain, (~l1_orders_2('#skF_6') | u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_666, c_21937])).
% 14.08/6.74  tff(c_21949, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_94, c_74, c_21940])).
% 14.08/6.74  tff(c_500, plain, (![A_134]: (r2_hidden(A_134, u1_struct_0('#skF_6')) | ~m1_subset_1(A_134, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_492])).
% 14.08/6.74  tff(c_4190, plain, (![B_393, A_394]: (u1_struct_0('#skF_6')=B_393 | ~m1_subset_1(B_393, k1_zfmisc_1(A_394)) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_394)) | v1_xboole_0(B_393) | ~m1_subset_1('#skF_2'(A_394, u1_struct_0('#skF_6'), B_393), B_393) | ~m1_subset_1('#skF_2'(A_394, u1_struct_0('#skF_6'), B_393), '#skF_7'))), inference(resolution, [status(thm)], [c_500, c_4117])).
% 14.08/6.74  tff(c_4199, plain, (![A_11]: (v1_xboole_0(A_11) | ~m1_subset_1('#skF_2'(A_11, u1_struct_0('#skF_6'), A_11), '#skF_7') | u1_struct_0('#skF_6')=A_11 | ~m1_subset_1(A_11, k1_zfmisc_1(A_11)) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_12, c_4190])).
% 14.08/6.74  tff(c_4220, plain, (![A_395]: (v1_xboole_0(A_395) | ~m1_subset_1('#skF_2'(A_395, u1_struct_0('#skF_6'), A_395), '#skF_7') | u1_struct_0('#skF_6')=A_395 | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(A_395)))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_4199])).
% 14.08/6.74  tff(c_4228, plain, (v1_xboole_0('#skF_7') | u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7')) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_12, c_4220])).
% 14.08/6.74  tff(c_4235, plain, (v1_xboole_0('#skF_7') | u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_4228])).
% 14.08/6.74  tff(c_4236, plain, (u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_4235])).
% 14.08/6.74  tff(c_4237, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_4236])).
% 14.08/6.74  tff(c_22004, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_21949, c_4237])).
% 14.08/6.74  tff(c_22043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_22004])).
% 14.08/6.74  tff(c_22044, plain, (u1_struct_0('#skF_6')='#skF_7' | r2_hidden('#skF_2'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6')), '#skF_7')), inference(splitRight, [status(thm)], [c_21789])).
% 14.08/6.74  tff(c_22053, plain, (r2_hidden('#skF_2'(u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_6')), '#skF_7')), inference(splitLeft, [status(thm)], [c_22044])).
% 14.08/6.74  tff(c_22056, plain, (v1_xboole_0(u1_struct_0('#skF_6')) | v1_xboole_0('#skF_7') | u1_struct_0('#skF_6')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_22053, c_13922])).
% 14.08/6.74  tff(c_22078, plain, (v1_xboole_0(u1_struct_0('#skF_6')) | v1_xboole_0('#skF_7') | u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_22056])).
% 14.08/6.74  tff(c_22079, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_72, c_218, c_22078])).
% 14.08/6.74  tff(c_22150, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_22079, c_4237])).
% 14.08/6.74  tff(c_22189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_22150])).
% 14.08/6.74  tff(c_22190, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_22044])).
% 14.08/6.74  tff(c_22244, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_22190, c_4237])).
% 14.08/6.74  tff(c_22283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_22244])).
% 14.08/6.74  tff(c_22284, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_4236])).
% 14.08/6.74  tff(c_166, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_92])).
% 14.08/6.74  tff(c_22310, plain, (v1_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_22284, c_166])).
% 14.08/6.74  tff(c_22315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_22310])).
% 14.08/6.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.08/6.74  
% 14.08/6.74  Inference rules
% 14.08/6.74  ----------------------
% 14.08/6.74  #Ref     : 0
% 14.08/6.74  #Sup     : 4738
% 14.08/6.74  #Fact    : 16
% 14.08/6.74  #Define  : 0
% 14.08/6.74  #Split   : 18
% 14.08/6.74  #Chain   : 0
% 14.08/6.74  #Close   : 0
% 14.08/6.74  
% 14.08/6.74  Ordering : KBO
% 14.08/6.74  
% 14.08/6.74  Simplification rules
% 14.08/6.74  ----------------------
% 14.08/6.74  #Subsume      : 631
% 14.08/6.74  #Demod        : 939
% 14.08/6.74  #Tautology    : 250
% 14.08/6.74  #SimpNegUnit  : 103
% 14.08/6.74  #BackRed      : 268
% 14.08/6.74  
% 14.08/6.74  #Partial instantiations: 0
% 14.08/6.74  #Strategies tried      : 1
% 14.08/6.74  
% 14.08/6.74  Timing (in seconds)
% 14.08/6.74  ----------------------
% 14.08/6.74  Preprocessing        : 0.37
% 14.08/6.74  Parsing              : 0.19
% 14.08/6.74  CNF conversion       : 0.03
% 14.08/6.74  Main loop            : 5.61
% 14.08/6.74  Inferencing          : 1.00
% 14.08/6.74  Reduction            : 1.07
% 14.08/6.74  Demodulation         : 0.75
% 14.08/6.74  BG Simplification    : 0.14
% 14.08/6.74  Subsumption          : 3.04
% 14.08/6.75  Abstraction          : 0.18
% 14.08/6.75  MUC search           : 0.00
% 14.08/6.75  Cooper               : 0.00
% 14.08/6.75  Total                : 6.03
% 14.08/6.75  Index Insertion      : 0.00
% 14.08/6.75  Index Deletion       : 0.00
% 14.08/6.75  Index Matching       : 0.00
% 14.08/6.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
