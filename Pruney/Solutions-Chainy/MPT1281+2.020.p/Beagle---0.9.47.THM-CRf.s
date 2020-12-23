%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:16 EST 2020

% Result     : Theorem 13.69s
% Output     : CNFRefutation 13.82s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 153 expanded)
%              Number of leaves         :   34 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  114 ( 323 expanded)
%              Number of equality atoms :   23 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
           => k2_tops_1(A,k1_tops_1(A,B)) = k2_tops_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tops_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_40,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_32,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(k1_tops_1(A_45,B_46),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2039,plain,(
    ! [A_275,B_276] :
      ( k2_tops_1(A_275,k1_tops_1(A_275,B_276)) = k2_tops_1(A_275,B_276)
      | ~ v5_tops_1(B_276,A_275)
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0(A_275)))
      | ~ l1_pre_topc(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2048,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2039])).

tff(c_2057,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_2048])).

tff(c_552,plain,(
    ! [A_163,B_164] :
      ( m1_subset_1(k2_tops_1(A_163,B_164),k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_556,plain,(
    ! [A_163,B_164] :
      ( r1_tarski(k2_tops_1(A_163,B_164),u1_struct_0(A_163))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_552,c_28])).

tff(c_2062,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2057,c_556])).

tff(c_2069,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2062])).

tff(c_2073,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2069])).

tff(c_2076,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2073])).

tff(c_2083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2076])).

tff(c_2084,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2069])).

tff(c_2085,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2069])).

tff(c_2254,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2085,c_28])).

tff(c_1827,plain,(
    ! [A_263,B_264] :
      ( k4_subset_1(u1_struct_0(A_263),B_264,k2_tops_1(A_263,B_264)) = k2_pre_topc(A_263,B_264)
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ l1_pre_topc(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4591,plain,(
    ! [A_348,B_349] :
      ( k4_subset_1(u1_struct_0(A_348),k1_tops_1(A_348,B_349),k2_tops_1(A_348,k1_tops_1(A_348,B_349))) = k2_pre_topc(A_348,k1_tops_1(A_348,B_349))
      | ~ m1_subset_1(B_349,k1_zfmisc_1(u1_struct_0(A_348)))
      | ~ l1_pre_topc(A_348) ) ),
    inference(resolution,[status(thm)],[c_32,c_1827])).

tff(c_4610,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2057,c_4591])).

tff(c_4618,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_4610])).

tff(c_30,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(A_43,k1_zfmisc_1(B_44))
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1199,plain,(
    ! [A_237,C_238,B_239] :
      ( k4_subset_1(A_237,C_238,B_239) = k4_subset_1(A_237,B_239,C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(A_237))
      | ~ m1_subset_1(B_239,k1_zfmisc_1(A_237)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6076,plain,(
    ! [A_404,B_405,B_406] :
      ( k4_subset_1(u1_struct_0(A_404),k1_tops_1(A_404,B_405),B_406) = k4_subset_1(u1_struct_0(A_404),B_406,k1_tops_1(A_404,B_405))
      | ~ m1_subset_1(B_406,k1_zfmisc_1(u1_struct_0(A_404)))
      | ~ m1_subset_1(B_405,k1_zfmisc_1(u1_struct_0(A_404)))
      | ~ l1_pre_topc(A_404) ) ),
    inference(resolution,[status(thm)],[c_32,c_1199])).

tff(c_25396,plain,(
    ! [A_818,B_819,A_820] :
      ( k4_subset_1(u1_struct_0(A_818),k1_tops_1(A_818,B_819),A_820) = k4_subset_1(u1_struct_0(A_818),A_820,k1_tops_1(A_818,B_819))
      | ~ m1_subset_1(B_819,k1_zfmisc_1(u1_struct_0(A_818)))
      | ~ l1_pre_topc(A_818)
      | ~ r1_tarski(A_820,u1_struct_0(A_818)) ) ),
    inference(resolution,[status(thm)],[c_30,c_6076])).

tff(c_25411,plain,(
    ! [A_820] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),A_820) = k4_subset_1(u1_struct_0('#skF_1'),A_820,k1_tops_1('#skF_1','#skF_2'))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_820,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_44,c_25396])).

tff(c_26076,plain,(
    ! [A_829] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),A_829) = k4_subset_1(u1_struct_0('#skF_1'),A_829,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_829,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_25411])).

tff(c_34,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k2_tops_1(A_47,B_48),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1018,plain,(
    ! [A_227,B_228,C_229] :
      ( k4_subset_1(A_227,B_228,C_229) = k2_xboole_0(B_228,C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(A_227))
      | ~ m1_subset_1(B_228,k1_zfmisc_1(A_227)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2351,plain,(
    ! [B_281,B_282,A_283] :
      ( k4_subset_1(B_281,B_282,A_283) = k2_xboole_0(B_282,A_283)
      | ~ m1_subset_1(B_282,k1_zfmisc_1(B_281))
      | ~ r1_tarski(A_283,B_281) ) ),
    inference(resolution,[status(thm)],[c_30,c_1018])).

tff(c_19356,plain,(
    ! [A_698,B_699,A_700] :
      ( k4_subset_1(u1_struct_0(A_698),k2_tops_1(A_698,B_699),A_700) = k2_xboole_0(k2_tops_1(A_698,B_699),A_700)
      | ~ r1_tarski(A_700,u1_struct_0(A_698))
      | ~ m1_subset_1(B_699,k1_zfmisc_1(u1_struct_0(A_698)))
      | ~ l1_pre_topc(A_698) ) ),
    inference(resolution,[status(thm)],[c_34,c_2351])).

tff(c_19369,plain,(
    ! [A_700] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),A_700) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),A_700)
      | ~ r1_tarski(A_700,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_19356])).

tff(c_19384,plain,(
    ! [A_700] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),A_700) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),A_700)
      | ~ r1_tarski(A_700,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_19369])).

tff(c_26096,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26076,c_19384])).

tff(c_26210,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_2254,c_4618,c_26096])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26432,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26210,c_4])).

tff(c_26460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_26432])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.69/6.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.82/6.32  
% 13.82/6.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.82/6.32  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 13.82/6.32  
% 13.82/6.32  %Foreground sorts:
% 13.82/6.32  
% 13.82/6.32  
% 13.82/6.32  %Background operators:
% 13.82/6.32  
% 13.82/6.32  
% 13.82/6.32  %Foreground operators:
% 13.82/6.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.82/6.32  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 13.82/6.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.82/6.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.82/6.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.82/6.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.82/6.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.82/6.32  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 13.82/6.32  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 13.82/6.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.82/6.32  tff('#skF_2', type, '#skF_2': $i).
% 13.82/6.32  tff('#skF_1', type, '#skF_1': $i).
% 13.82/6.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.82/6.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.82/6.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.82/6.32  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 13.82/6.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.82/6.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.82/6.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.82/6.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.82/6.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.82/6.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.82/6.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 13.82/6.32  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 13.82/6.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.82/6.32  
% 13.82/6.34  tff(f_105, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tops_1)).
% 13.82/6.34  tff(f_73, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 13.82/6.34  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => (k2_tops_1(A, k1_tops_1(A, B)) = k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_tops_1)).
% 13.82/6.34  tff(f_79, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 13.82/6.34  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.82/6.34  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 13.82/6.34  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 13.82/6.34  tff(f_63, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 13.82/6.34  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.82/6.34  tff(c_40, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.82/6.34  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.82/6.34  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.82/6.34  tff(c_32, plain, (![A_45, B_46]: (m1_subset_1(k1_tops_1(A_45, B_46), k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.82/6.34  tff(c_42, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.82/6.34  tff(c_2039, plain, (![A_275, B_276]: (k2_tops_1(A_275, k1_tops_1(A_275, B_276))=k2_tops_1(A_275, B_276) | ~v5_tops_1(B_276, A_275) | ~m1_subset_1(B_276, k1_zfmisc_1(u1_struct_0(A_275))) | ~l1_pre_topc(A_275))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.82/6.34  tff(c_2048, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_2039])).
% 13.82/6.34  tff(c_2057, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_2048])).
% 13.82/6.34  tff(c_552, plain, (![A_163, B_164]: (m1_subset_1(k2_tops_1(A_163, B_164), k1_zfmisc_1(u1_struct_0(A_163))) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.82/6.34  tff(c_28, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | ~m1_subset_1(A_43, k1_zfmisc_1(B_44)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.82/6.34  tff(c_556, plain, (![A_163, B_164]: (r1_tarski(k2_tops_1(A_163, B_164), u1_struct_0(A_163)) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163))), inference(resolution, [status(thm)], [c_552, c_28])).
% 13.82/6.34  tff(c_2062, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2057, c_556])).
% 13.82/6.34  tff(c_2069, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2062])).
% 13.82/6.34  tff(c_2073, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2069])).
% 13.82/6.34  tff(c_2076, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2073])).
% 13.82/6.34  tff(c_2083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2076])).
% 13.82/6.34  tff(c_2084, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_2069])).
% 13.82/6.34  tff(c_2085, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_2069])).
% 13.82/6.34  tff(c_2254, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2085, c_28])).
% 13.82/6.34  tff(c_1827, plain, (![A_263, B_264]: (k4_subset_1(u1_struct_0(A_263), B_264, k2_tops_1(A_263, B_264))=k2_pre_topc(A_263, B_264) | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0(A_263))) | ~l1_pre_topc(A_263))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.82/6.34  tff(c_4591, plain, (![A_348, B_349]: (k4_subset_1(u1_struct_0(A_348), k1_tops_1(A_348, B_349), k2_tops_1(A_348, k1_tops_1(A_348, B_349)))=k2_pre_topc(A_348, k1_tops_1(A_348, B_349)) | ~m1_subset_1(B_349, k1_zfmisc_1(u1_struct_0(A_348))) | ~l1_pre_topc(A_348))), inference(resolution, [status(thm)], [c_32, c_1827])).
% 13.82/6.34  tff(c_4610, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2057, c_4591])).
% 13.82/6.34  tff(c_4618, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_4610])).
% 13.82/6.34  tff(c_30, plain, (![A_43, B_44]: (m1_subset_1(A_43, k1_zfmisc_1(B_44)) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.82/6.34  tff(c_1199, plain, (![A_237, C_238, B_239]: (k4_subset_1(A_237, C_238, B_239)=k4_subset_1(A_237, B_239, C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(A_237)) | ~m1_subset_1(B_239, k1_zfmisc_1(A_237)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.82/6.34  tff(c_6076, plain, (![A_404, B_405, B_406]: (k4_subset_1(u1_struct_0(A_404), k1_tops_1(A_404, B_405), B_406)=k4_subset_1(u1_struct_0(A_404), B_406, k1_tops_1(A_404, B_405)) | ~m1_subset_1(B_406, k1_zfmisc_1(u1_struct_0(A_404))) | ~m1_subset_1(B_405, k1_zfmisc_1(u1_struct_0(A_404))) | ~l1_pre_topc(A_404))), inference(resolution, [status(thm)], [c_32, c_1199])).
% 13.82/6.34  tff(c_25396, plain, (![A_818, B_819, A_820]: (k4_subset_1(u1_struct_0(A_818), k1_tops_1(A_818, B_819), A_820)=k4_subset_1(u1_struct_0(A_818), A_820, k1_tops_1(A_818, B_819)) | ~m1_subset_1(B_819, k1_zfmisc_1(u1_struct_0(A_818))) | ~l1_pre_topc(A_818) | ~r1_tarski(A_820, u1_struct_0(A_818)))), inference(resolution, [status(thm)], [c_30, c_6076])).
% 13.82/6.34  tff(c_25411, plain, (![A_820]: (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), A_820)=k4_subset_1(u1_struct_0('#skF_1'), A_820, k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_820, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_44, c_25396])).
% 13.82/6.34  tff(c_26076, plain, (![A_829]: (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), A_829)=k4_subset_1(u1_struct_0('#skF_1'), A_829, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(A_829, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_25411])).
% 13.82/6.34  tff(c_34, plain, (![A_47, B_48]: (m1_subset_1(k2_tops_1(A_47, B_48), k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.82/6.34  tff(c_1018, plain, (![A_227, B_228, C_229]: (k4_subset_1(A_227, B_228, C_229)=k2_xboole_0(B_228, C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(A_227)) | ~m1_subset_1(B_228, k1_zfmisc_1(A_227)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.82/6.34  tff(c_2351, plain, (![B_281, B_282, A_283]: (k4_subset_1(B_281, B_282, A_283)=k2_xboole_0(B_282, A_283) | ~m1_subset_1(B_282, k1_zfmisc_1(B_281)) | ~r1_tarski(A_283, B_281))), inference(resolution, [status(thm)], [c_30, c_1018])).
% 13.82/6.34  tff(c_19356, plain, (![A_698, B_699, A_700]: (k4_subset_1(u1_struct_0(A_698), k2_tops_1(A_698, B_699), A_700)=k2_xboole_0(k2_tops_1(A_698, B_699), A_700) | ~r1_tarski(A_700, u1_struct_0(A_698)) | ~m1_subset_1(B_699, k1_zfmisc_1(u1_struct_0(A_698))) | ~l1_pre_topc(A_698))), inference(resolution, [status(thm)], [c_34, c_2351])).
% 13.82/6.34  tff(c_19369, plain, (![A_700]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), A_700)=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), A_700) | ~r1_tarski(A_700, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_19356])).
% 13.82/6.34  tff(c_19384, plain, (![A_700]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), A_700)=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), A_700) | ~r1_tarski(A_700, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_19369])).
% 13.82/6.34  tff(c_26096, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_26076, c_19384])).
% 13.82/6.34  tff(c_26210, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_2254, c_4618, c_26096])).
% 13.82/6.34  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.82/6.34  tff(c_26432, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_26210, c_4])).
% 13.82/6.34  tff(c_26460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_26432])).
% 13.82/6.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.82/6.34  
% 13.82/6.34  Inference rules
% 13.82/6.34  ----------------------
% 13.82/6.34  #Ref     : 0
% 13.82/6.34  #Sup     : 7054
% 13.82/6.34  #Fact    : 0
% 13.82/6.34  #Define  : 0
% 13.82/6.34  #Split   : 12
% 13.82/6.34  #Chain   : 0
% 13.82/6.34  #Close   : 0
% 13.82/6.34  
% 13.82/6.34  Ordering : KBO
% 13.82/6.34  
% 13.82/6.34  Simplification rules
% 13.82/6.34  ----------------------
% 13.82/6.34  #Subsume      : 1494
% 13.82/6.34  #Demod        : 2588
% 13.82/6.34  #Tautology    : 1840
% 13.82/6.34  #SimpNegUnit  : 5
% 13.82/6.34  #BackRed      : 4
% 13.82/6.34  
% 13.82/6.34  #Partial instantiations: 0
% 13.82/6.34  #Strategies tried      : 1
% 13.82/6.34  
% 13.82/6.34  Timing (in seconds)
% 13.82/6.34  ----------------------
% 13.82/6.34  Preprocessing        : 0.34
% 13.82/6.34  Parsing              : 0.19
% 13.82/6.34  CNF conversion       : 0.02
% 13.82/6.34  Main loop            : 5.17
% 13.82/6.34  Inferencing          : 0.83
% 13.82/6.34  Reduction            : 2.02
% 13.82/6.34  Demodulation         : 1.63
% 13.82/6.34  BG Simplification    : 0.12
% 13.82/6.34  Subsumption          : 1.90
% 13.82/6.34  Abstraction          : 0.19
% 13.82/6.34  MUC search           : 0.00
% 13.82/6.34  Cooper               : 0.00
% 13.82/6.34  Total                : 5.54
% 13.82/6.34  Index Insertion      : 0.00
% 13.82/6.34  Index Deletion       : 0.00
% 13.82/6.34  Index Matching       : 0.00
% 13.82/6.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
