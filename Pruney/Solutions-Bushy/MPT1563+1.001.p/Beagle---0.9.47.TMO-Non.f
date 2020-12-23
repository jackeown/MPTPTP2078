%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1563+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:04 EST 2020

% Result     : Timeout 59.44s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  310 (2205921 expanded)
%              Number of leaves         :   38 (788882 expanded)
%              Depth                    :   48
%              Number of atoms          : 1246 (14603336 expanded)
%              Number of equality atoms :  104 (966237 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_lattice3 > l1_struct_0 > l1_orders_2 > k7_domain_1 > k13_lattice3 > k2_tarski > k1_yellow_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_domain_1,type,(
    k7_domain_1: ( $i * $i * $i ) > $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_185,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_yellow_0(A,k7_domain_1(u1_struct_0(A),B,C)) = k13_lattice3(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_yellow_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k13_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_lattice3)).

tff(f_131,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k13_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_0)).

tff(f_166,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_lattice3(A,k2_tarski(C,D),B)
                     => ( r1_orders_2(A,B,C)
                        & r1_orders_2(A,B,D) ) )
                    & ( ( r1_orders_2(A,B,C)
                        & r1_orders_2(A,B,D) )
                     => r1_lattice3(A,k2_tarski(C,D),B) )
                    & ( r2_lattice3(A,k2_tarski(C,D),B)
                     => ( r1_orders_2(A,C,B)
                        & r1_orders_2(A,D,B) ) )
                    & ( ( r1_orders_2(A,C,B)
                        & r1_orders_2(A,D,B) )
                     => r2_lattice3(A,k2_tarski(C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_0)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => k7_domain_1(A,B,C) = k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r1_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r2_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_lattice3(A,B,D)
                   => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).

tff(f_49,axiom,(
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

tff(c_66,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_70,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_68,plain,(
    v1_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k13_lattice3(A_14,B_15,C_16),u1_struct_0(A_14))
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v1_lattice3(A_14)
      | ~ v5_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_348,plain,(
    ! [A_194,B_195,C_196] :
      ( r1_orders_2(A_194,B_195,k13_lattice3(A_194,B_195,C_196))
      | ~ m1_subset_1(k13_lattice3(A_194,B_195,C_196),u1_struct_0(A_194))
      | ~ m1_subset_1(C_196,u1_struct_0(A_194))
      | ~ m1_subset_1(B_195,u1_struct_0(A_194))
      | ~ l1_orders_2(A_194)
      | ~ v1_lattice3(A_194)
      | ~ v5_orders_2(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_351,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_orders_2(A_14,B_15,k13_lattice3(A_14,B_15,C_16))
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v1_lattice3(A_14)
      | ~ v5_orders_2(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_348])).

tff(c_343,plain,(
    ! [A_188,C_189,B_190] :
      ( r1_orders_2(A_188,C_189,k13_lattice3(A_188,B_190,C_189))
      | ~ m1_subset_1(k13_lattice3(A_188,B_190,C_189),u1_struct_0(A_188))
      | ~ m1_subset_1(C_189,u1_struct_0(A_188))
      | ~ m1_subset_1(B_190,u1_struct_0(A_188))
      | ~ l1_orders_2(A_188)
      | ~ v1_lattice3(A_188)
      | ~ v5_orders_2(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_346,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_orders_2(A_14,C_16,k13_lattice3(A_14,B_15,C_16))
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v1_lattice3(A_14)
      | ~ v5_orders_2(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_343])).

tff(c_487,plain,(
    ! [A_257,B_258,C_259,E_260] :
      ( r1_orders_2(A_257,k13_lattice3(A_257,B_258,C_259),E_260)
      | ~ r1_orders_2(A_257,C_259,E_260)
      | ~ r1_orders_2(A_257,B_258,E_260)
      | ~ m1_subset_1(E_260,u1_struct_0(A_257))
      | ~ m1_subset_1(k13_lattice3(A_257,B_258,C_259),u1_struct_0(A_257))
      | ~ m1_subset_1(C_259,u1_struct_0(A_257))
      | ~ m1_subset_1(B_258,u1_struct_0(A_257))
      | ~ l1_orders_2(A_257)
      | ~ v1_lattice3(A_257)
      | ~ v5_orders_2(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_491,plain,(
    ! [A_261,B_262,C_263,E_264] :
      ( r1_orders_2(A_261,k13_lattice3(A_261,B_262,C_263),E_264)
      | ~ r1_orders_2(A_261,C_263,E_264)
      | ~ r1_orders_2(A_261,B_262,E_264)
      | ~ m1_subset_1(E_264,u1_struct_0(A_261))
      | ~ m1_subset_1(C_263,u1_struct_0(A_261))
      | ~ m1_subset_1(B_262,u1_struct_0(A_261))
      | ~ l1_orders_2(A_261)
      | ~ v1_lattice3(A_261)
      | ~ v5_orders_2(A_261) ) ),
    inference(resolution,[status(thm)],[c_14,c_487])).

tff(c_36,plain,(
    ! [A_47,C_83,B_71,D_89] :
      ( r1_orders_2(A_47,C_83,'#skF_4'(A_47,B_71,C_83,D_89))
      | k13_lattice3(A_47,B_71,C_83) = D_89
      | ~ r1_orders_2(A_47,C_83,D_89)
      | ~ r1_orders_2(A_47,B_71,D_89)
      | ~ m1_subset_1(D_89,u1_struct_0(A_47))
      | ~ m1_subset_1(C_83,u1_struct_0(A_47))
      | ~ m1_subset_1(B_71,u1_struct_0(A_47))
      | ~ l1_orders_2(A_47)
      | ~ v1_lattice3(A_47)
      | ~ v5_orders_2(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_402,plain,(
    ! [A_228,D_229,B_230,C_231] :
      ( ~ r1_orders_2(A_228,D_229,'#skF_4'(A_228,B_230,C_231,D_229))
      | k13_lattice3(A_228,B_230,C_231) = D_229
      | ~ r1_orders_2(A_228,C_231,D_229)
      | ~ r1_orders_2(A_228,B_230,D_229)
      | ~ m1_subset_1(D_229,u1_struct_0(A_228))
      | ~ m1_subset_1(C_231,u1_struct_0(A_228))
      | ~ m1_subset_1(B_230,u1_struct_0(A_228))
      | ~ l1_orders_2(A_228)
      | ~ v1_lattice3(A_228)
      | ~ v5_orders_2(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_411,plain,(
    ! [A_47,B_71,D_89] :
      ( k13_lattice3(A_47,B_71,D_89) = D_89
      | ~ r1_orders_2(A_47,D_89,D_89)
      | ~ r1_orders_2(A_47,B_71,D_89)
      | ~ m1_subset_1(D_89,u1_struct_0(A_47))
      | ~ m1_subset_1(B_71,u1_struct_0(A_47))
      | ~ l1_orders_2(A_47)
      | ~ v1_lattice3(A_47)
      | ~ v5_orders_2(A_47) ) ),
    inference(resolution,[status(thm)],[c_36,c_402])).

tff(c_1626,plain,(
    ! [A_440,B_441,B_442,C_443] :
      ( k13_lattice3(A_440,B_441,k13_lattice3(A_440,B_442,C_443)) = k13_lattice3(A_440,B_442,C_443)
      | ~ r1_orders_2(A_440,B_441,k13_lattice3(A_440,B_442,C_443))
      | ~ m1_subset_1(B_441,u1_struct_0(A_440))
      | ~ r1_orders_2(A_440,C_443,k13_lattice3(A_440,B_442,C_443))
      | ~ r1_orders_2(A_440,B_442,k13_lattice3(A_440,B_442,C_443))
      | ~ m1_subset_1(k13_lattice3(A_440,B_442,C_443),u1_struct_0(A_440))
      | ~ m1_subset_1(C_443,u1_struct_0(A_440))
      | ~ m1_subset_1(B_442,u1_struct_0(A_440))
      | ~ l1_orders_2(A_440)
      | ~ v1_lattice3(A_440)
      | ~ v5_orders_2(A_440) ) ),
    inference(resolution,[status(thm)],[c_491,c_411])).

tff(c_3891,plain,(
    ! [A_496,B_497,C_498] :
      ( k13_lattice3(A_496,B_497,k13_lattice3(A_496,B_497,C_498)) = k13_lattice3(A_496,B_497,C_498)
      | ~ r1_orders_2(A_496,C_498,k13_lattice3(A_496,B_497,C_498))
      | ~ r1_orders_2(A_496,B_497,k13_lattice3(A_496,B_497,C_498))
      | ~ m1_subset_1(k13_lattice3(A_496,B_497,C_498),u1_struct_0(A_496))
      | ~ m1_subset_1(C_498,u1_struct_0(A_496))
      | ~ m1_subset_1(B_497,u1_struct_0(A_496))
      | ~ l1_orders_2(A_496)
      | ~ v1_lattice3(A_496)
      | ~ v5_orders_2(A_496) ) ),
    inference(resolution,[status(thm)],[c_351,c_1626])).

tff(c_28092,plain,(
    ! [A_838,B_839,C_840] :
      ( k13_lattice3(A_838,B_839,k13_lattice3(A_838,B_839,C_840)) = k13_lattice3(A_838,B_839,C_840)
      | ~ r1_orders_2(A_838,B_839,k13_lattice3(A_838,B_839,C_840))
      | ~ m1_subset_1(k13_lattice3(A_838,B_839,C_840),u1_struct_0(A_838))
      | ~ m1_subset_1(C_840,u1_struct_0(A_838))
      | ~ m1_subset_1(B_839,u1_struct_0(A_838))
      | ~ l1_orders_2(A_838)
      | ~ v1_lattice3(A_838)
      | ~ v5_orders_2(A_838) ) ),
    inference(resolution,[status(thm)],[c_346,c_3891])).

tff(c_31324,plain,(
    ! [A_864,B_865,C_866] :
      ( k13_lattice3(A_864,B_865,k13_lattice3(A_864,B_865,C_866)) = k13_lattice3(A_864,B_865,C_866)
      | ~ m1_subset_1(k13_lattice3(A_864,B_865,C_866),u1_struct_0(A_864))
      | ~ m1_subset_1(C_866,u1_struct_0(A_864))
      | ~ m1_subset_1(B_865,u1_struct_0(A_864))
      | ~ l1_orders_2(A_864)
      | ~ v1_lattice3(A_864)
      | ~ v5_orders_2(A_864) ) ),
    inference(resolution,[status(thm)],[c_351,c_28092])).

tff(c_31904,plain,(
    ! [A_869,B_870,C_871] :
      ( k13_lattice3(A_869,B_870,k13_lattice3(A_869,B_870,C_871)) = k13_lattice3(A_869,B_870,C_871)
      | ~ m1_subset_1(C_871,u1_struct_0(A_869))
      | ~ m1_subset_1(B_870,u1_struct_0(A_869))
      | ~ l1_orders_2(A_869)
      | ~ v1_lattice3(A_869)
      | ~ v5_orders_2(A_869) ) ),
    inference(resolution,[status(thm)],[c_14,c_31324])).

tff(c_31920,plain,(
    ! [B_870] :
      ( k13_lattice3('#skF_5',B_870,k13_lattice3('#skF_5',B_870,'#skF_7')) = k13_lattice3('#skF_5',B_870,'#skF_7')
      | ~ m1_subset_1(B_870,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_lattice3('#skF_5')
      | ~ v5_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_31904])).

tff(c_31940,plain,(
    ! [B_872] :
      ( k13_lattice3('#skF_5',B_872,k13_lattice3('#skF_5',B_872,'#skF_7')) = k13_lattice3('#skF_5',B_872,'#skF_7')
      | ~ m1_subset_1(B_872,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_31920])).

tff(c_31984,plain,(
    k13_lattice3('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7')) = k13_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_31940])).

tff(c_32058,plain,
    ( r1_orders_2('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_31984,c_351])).

tff(c_32139,plain,
    ( r1_orders_2('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_32058])).

tff(c_32149,plain,(
    ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_32139])).

tff(c_32152,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_32149])).

tff(c_32156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_32152])).

tff(c_32158,plain,(
    m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_32139])).

tff(c_32157,plain,(
    r1_orders_2('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_32139])).

tff(c_32061,plain,
    ( r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_31984,c_346])).

tff(c_32141,plain,
    ( r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_32061])).

tff(c_32835,plain,(
    r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32158,c_32141])).

tff(c_436,plain,(
    ! [A_243,B_244,C_245,D_246] :
      ( r1_orders_2(A_243,B_244,'#skF_4'(A_243,B_244,C_245,D_246))
      | k13_lattice3(A_243,B_244,C_245) = D_246
      | ~ r1_orders_2(A_243,C_245,D_246)
      | ~ r1_orders_2(A_243,B_244,D_246)
      | ~ m1_subset_1(D_246,u1_struct_0(A_243))
      | ~ m1_subset_1(C_245,u1_struct_0(A_243))
      | ~ m1_subset_1(B_244,u1_struct_0(A_243))
      | ~ l1_orders_2(A_243)
      | ~ v1_lattice3(A_243)
      | ~ v5_orders_2(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_34,plain,(
    ! [A_47,D_89,B_71,C_83] :
      ( ~ r1_orders_2(A_47,D_89,'#skF_4'(A_47,B_71,C_83,D_89))
      | k13_lattice3(A_47,B_71,C_83) = D_89
      | ~ r1_orders_2(A_47,C_83,D_89)
      | ~ r1_orders_2(A_47,B_71,D_89)
      | ~ m1_subset_1(D_89,u1_struct_0(A_47))
      | ~ m1_subset_1(C_83,u1_struct_0(A_47))
      | ~ m1_subset_1(B_71,u1_struct_0(A_47))
      | ~ l1_orders_2(A_47)
      | ~ v1_lattice3(A_47)
      | ~ v5_orders_2(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_442,plain,(
    ! [A_247,D_248,C_249] :
      ( k13_lattice3(A_247,D_248,C_249) = D_248
      | ~ r1_orders_2(A_247,C_249,D_248)
      | ~ r1_orders_2(A_247,D_248,D_248)
      | ~ m1_subset_1(C_249,u1_struct_0(A_247))
      | ~ m1_subset_1(D_248,u1_struct_0(A_247))
      | ~ l1_orders_2(A_247)
      | ~ v1_lattice3(A_247)
      | ~ v5_orders_2(A_247) ) ),
    inference(resolution,[status(thm)],[c_436,c_34])).

tff(c_462,plain,(
    ! [A_14,B_15,C_16] :
      ( k13_lattice3(A_14,k13_lattice3(A_14,B_15,C_16),C_16) = k13_lattice3(A_14,B_15,C_16)
      | ~ r1_orders_2(A_14,k13_lattice3(A_14,B_15,C_16),k13_lattice3(A_14,B_15,C_16))
      | ~ m1_subset_1(k13_lattice3(A_14,B_15,C_16),u1_struct_0(A_14))
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v1_lattice3(A_14)
      | ~ v5_orders_2(A_14) ) ),
    inference(resolution,[status(thm)],[c_346,c_442])).

tff(c_32863,plain,
    ( k13_lattice3('#skF_5',k13_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7') = k13_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_32835,c_462])).

tff(c_32912,plain,(
    k13_lattice3('#skF_5',k13_lattice3('#skF_5','#skF_6','#skF_7'),'#skF_7') = k13_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_32158,c_32863])).

tff(c_33150,plain,
    ( r1_orders_2('#skF_5','#skF_7',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_32912,c_346])).

tff(c_33224,plain,(
    r1_orders_2('#skF_5','#skF_7',k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_32158,c_62,c_33150])).

tff(c_48,plain,(
    ! [A_93,C_105,D_107,B_101] :
      ( r2_lattice3(A_93,k2_tarski(C_105,D_107),B_101)
      | ~ r1_orders_2(A_93,D_107,B_101)
      | ~ r1_orders_2(A_93,C_105,B_101)
      | ~ m1_subset_1(D_107,u1_struct_0(A_93))
      | ~ m1_subset_1(C_105,u1_struct_0(A_93))
      | ~ m1_subset_1(B_101,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_16,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_80,plain,(
    ! [A_119,B_120,C_121] :
      ( k7_domain_1(A_119,B_120,C_121) = k2_tarski(B_120,C_121)
      | ~ m1_subset_1(C_121,A_119)
      | ~ m1_subset_1(B_120,A_119)
      | v1_xboole_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_88,plain,(
    ! [B_120] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_120,'#skF_7') = k2_tarski(B_120,'#skF_7')
      | ~ m1_subset_1(B_120,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_62,c_80])).

tff(c_90,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_18,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_95,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_18])).

tff(c_96,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_99,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_99])).

tff(c_104,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v1_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,
    ( ~ v1_lattice3('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_109])).

tff(c_116,plain,(
    ! [B_124] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_124,'#skF_7') = k2_tarski(B_124,'#skF_7')
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_131,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7') = k2_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_116])).

tff(c_60,plain,(
    k1_yellow_0('#skF_5',k7_domain_1(u1_struct_0('#skF_5'),'#skF_6','#skF_7')) != k13_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_137,plain,(
    k1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) != k13_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_60])).

tff(c_490,plain,(
    ! [A_14,B_15,C_16,E_260] :
      ( r1_orders_2(A_14,k13_lattice3(A_14,B_15,C_16),E_260)
      | ~ r1_orders_2(A_14,C_16,E_260)
      | ~ r1_orders_2(A_14,B_15,E_260)
      | ~ m1_subset_1(E_260,u1_struct_0(A_14))
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v1_lattice3(A_14)
      | ~ v5_orders_2(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_487])).

tff(c_31922,plain,(
    ! [B_870] :
      ( k13_lattice3('#skF_5',B_870,k13_lattice3('#skF_5',B_870,'#skF_6')) = k13_lattice3('#skF_5',B_870,'#skF_6')
      | ~ m1_subset_1(B_870,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_lattice3('#skF_5')
      | ~ v5_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_31904])).

tff(c_32368,plain,(
    ! [B_876] :
      ( k13_lattice3('#skF_5',B_876,k13_lattice3('#skF_5',B_876,'#skF_6')) = k13_lattice3('#skF_5',B_876,'#skF_6')
      | ~ m1_subset_1(B_876,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_31922])).

tff(c_32413,plain,(
    k13_lattice3('#skF_5','#skF_7',k13_lattice3('#skF_5','#skF_7','#skF_6')) = k13_lattice3('#skF_5','#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_32368])).

tff(c_32489,plain,
    ( r1_orders_2('#skF_5','#skF_7',k13_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_32413,c_351])).

tff(c_32570,plain,
    ( r1_orders_2('#skF_5','#skF_7',k13_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_62,c_32489])).

tff(c_32580,plain,(
    ~ m1_subset_1(k13_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_32570])).

tff(c_32583,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_32580])).

tff(c_32587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_62,c_64,c_32583])).

tff(c_32589,plain,(
    m1_subset_1(k13_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_32570])).

tff(c_32492,plain,
    ( r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_32413,c_346])).

tff(c_32572,plain,
    ( r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_62,c_32492])).

tff(c_33650,plain,(
    r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32589,c_32572])).

tff(c_33678,plain,
    ( k13_lattice3('#skF_5',k13_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_6') = k13_lattice3('#skF_5','#skF_7','#skF_6')
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_33650,c_462])).

tff(c_33727,plain,(
    k13_lattice3('#skF_5',k13_lattice3('#skF_5','#skF_7','#skF_6'),'#skF_6') = k13_lattice3('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_62,c_64,c_32589,c_33678])).

tff(c_33965,plain,
    ( r1_orders_2('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_33727,c_346])).

tff(c_34039,plain,(
    r1_orders_2('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_32589,c_64,c_33965])).

tff(c_32588,plain,(
    r1_orders_2('#skF_5','#skF_7',k13_lattice3('#skF_5','#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_32570])).

tff(c_32,plain,(
    ! [A_22,B_36,C_43] :
      ( m1_subset_1('#skF_2'(A_22,B_36,C_43),u1_struct_0(A_22))
      | r1_yellow_0(A_22,B_36)
      | ~ r2_lattice3(A_22,B_36,C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    ! [A_22,B_36,C_43] :
      ( r2_lattice3(A_22,B_36,'#skF_2'(A_22,B_36,C_43))
      | r1_yellow_0(A_22,B_36)
      | ~ r2_lattice3(A_22,B_36,C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_290,plain,(
    ! [A_170,D_171,B_172,C_173] :
      ( r1_orders_2(A_170,D_171,B_172)
      | ~ r2_lattice3(A_170,k2_tarski(C_173,D_171),B_172)
      | ~ m1_subset_1(D_171,u1_struct_0(A_170))
      | ~ m1_subset_1(C_173,u1_struct_0(A_170))
      | ~ m1_subset_1(B_172,u1_struct_0(A_170))
      | ~ l1_orders_2(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_598,plain,(
    ! [A_297,D_298,C_299,C_300] :
      ( r1_orders_2(A_297,D_298,'#skF_2'(A_297,k2_tarski(C_299,D_298),C_300))
      | ~ m1_subset_1(D_298,u1_struct_0(A_297))
      | ~ m1_subset_1(C_299,u1_struct_0(A_297))
      | ~ m1_subset_1('#skF_2'(A_297,k2_tarski(C_299,D_298),C_300),u1_struct_0(A_297))
      | r1_yellow_0(A_297,k2_tarski(C_299,D_298))
      | ~ r2_lattice3(A_297,k2_tarski(C_299,D_298),C_300)
      | ~ m1_subset_1(C_300,u1_struct_0(A_297))
      | ~ l1_orders_2(A_297)
      | ~ v5_orders_2(A_297) ) ),
    inference(resolution,[status(thm)],[c_30,c_290])).

tff(c_603,plain,(
    ! [A_301,D_302,C_303,C_304] :
      ( r1_orders_2(A_301,D_302,'#skF_2'(A_301,k2_tarski(C_303,D_302),C_304))
      | ~ m1_subset_1(D_302,u1_struct_0(A_301))
      | ~ m1_subset_1(C_303,u1_struct_0(A_301))
      | r1_yellow_0(A_301,k2_tarski(C_303,D_302))
      | ~ r2_lattice3(A_301,k2_tarski(C_303,D_302),C_304)
      | ~ m1_subset_1(C_304,u1_struct_0(A_301))
      | ~ l1_orders_2(A_301)
      | ~ v5_orders_2(A_301) ) ),
    inference(resolution,[status(thm)],[c_32,c_598])).

tff(c_28,plain,(
    ! [A_22,C_43,B_36] :
      ( ~ r1_orders_2(A_22,C_43,'#skF_2'(A_22,B_36,C_43))
      | r1_yellow_0(A_22,B_36)
      | ~ r2_lattice3(A_22,B_36,C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_612,plain,(
    ! [C_305,A_306,C_307] :
      ( ~ m1_subset_1(C_305,u1_struct_0(A_306))
      | r1_yellow_0(A_306,k2_tarski(C_305,C_307))
      | ~ r2_lattice3(A_306,k2_tarski(C_305,C_307),C_307)
      | ~ m1_subset_1(C_307,u1_struct_0(A_306))
      | ~ l1_orders_2(A_306)
      | ~ v5_orders_2(A_306) ) ),
    inference(resolution,[status(thm)],[c_603,c_28])).

tff(c_617,plain,(
    ! [A_93,C_105,B_101] :
      ( r1_yellow_0(A_93,k2_tarski(C_105,B_101))
      | ~ v5_orders_2(A_93)
      | ~ r1_orders_2(A_93,B_101,B_101)
      | ~ r1_orders_2(A_93,C_105,B_101)
      | ~ m1_subset_1(C_105,u1_struct_0(A_93))
      | ~ m1_subset_1(B_101,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93) ) ),
    inference(resolution,[status(thm)],[c_48,c_612])).

tff(c_33680,plain,(
    ! [C_105] :
      ( r1_yellow_0('#skF_5',k2_tarski(C_105,k13_lattice3('#skF_5','#skF_7','#skF_6')))
      | ~ v5_orders_2('#skF_5')
      | ~ r1_orders_2('#skF_5',C_105,k13_lattice3('#skF_5','#skF_7','#skF_6'))
      | ~ m1_subset_1(C_105,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_33650,c_617])).

tff(c_36003,plain,(
    ! [C_901] :
      ( r1_yellow_0('#skF_5',k2_tarski(C_901,k13_lattice3('#skF_5','#skF_7','#skF_6')))
      | ~ r1_orders_2('#skF_5',C_901,k13_lattice3('#skF_5','#skF_7','#skF_6'))
      | ~ m1_subset_1(C_901,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32589,c_70,c_33680])).

tff(c_8,plain,(
    ! [A_2,B_9,C_10] :
      ( m1_subset_1('#skF_1'(A_2,B_9,C_10),u1_struct_0(A_2))
      | k1_yellow_0(A_2,B_9) = C_10
      | ~ r2_lattice3(A_2,B_9,C_10)
      | ~ r1_yellow_0(A_2,B_9)
      | ~ m1_subset_1(C_10,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_2,B_9,C_10] :
      ( r2_lattice3(A_2,B_9,'#skF_1'(A_2,B_9,C_10))
      | k1_yellow_0(A_2,B_9) = C_10
      | ~ r2_lattice3(A_2,B_9,C_10)
      | ~ r1_yellow_0(A_2,B_9)
      | ~ m1_subset_1(C_10,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_666,plain,(
    ! [A_330,D_331,C_332,C_333] :
      ( r1_orders_2(A_330,D_331,'#skF_1'(A_330,k2_tarski(C_332,D_331),C_333))
      | ~ m1_subset_1(D_331,u1_struct_0(A_330))
      | ~ m1_subset_1(C_332,u1_struct_0(A_330))
      | ~ m1_subset_1('#skF_1'(A_330,k2_tarski(C_332,D_331),C_333),u1_struct_0(A_330))
      | k1_yellow_0(A_330,k2_tarski(C_332,D_331)) = C_333
      | ~ r2_lattice3(A_330,k2_tarski(C_332,D_331),C_333)
      | ~ r1_yellow_0(A_330,k2_tarski(C_332,D_331))
      | ~ m1_subset_1(C_333,u1_struct_0(A_330))
      | ~ l1_orders_2(A_330) ) ),
    inference(resolution,[status(thm)],[c_6,c_290])).

tff(c_743,plain,(
    ! [A_354,D_355,C_356,C_357] :
      ( r1_orders_2(A_354,D_355,'#skF_1'(A_354,k2_tarski(C_356,D_355),C_357))
      | ~ m1_subset_1(D_355,u1_struct_0(A_354))
      | ~ m1_subset_1(C_356,u1_struct_0(A_354))
      | k1_yellow_0(A_354,k2_tarski(C_356,D_355)) = C_357
      | ~ r2_lattice3(A_354,k2_tarski(C_356,D_355),C_357)
      | ~ r1_yellow_0(A_354,k2_tarski(C_356,D_355))
      | ~ m1_subset_1(C_357,u1_struct_0(A_354))
      | ~ l1_orders_2(A_354) ) ),
    inference(resolution,[status(thm)],[c_8,c_666])).

tff(c_4,plain,(
    ! [A_2,C_10,B_9] :
      ( ~ r1_orders_2(A_2,C_10,'#skF_1'(A_2,B_9,C_10))
      | k1_yellow_0(A_2,B_9) = C_10
      | ~ r2_lattice3(A_2,B_9,C_10)
      | ~ r1_yellow_0(A_2,B_9)
      | ~ m1_subset_1(C_10,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_757,plain,(
    ! [C_362,A_363,C_364] :
      ( ~ m1_subset_1(C_362,u1_struct_0(A_363))
      | k1_yellow_0(A_363,k2_tarski(C_362,C_364)) = C_364
      | ~ r2_lattice3(A_363,k2_tarski(C_362,C_364),C_364)
      | ~ r1_yellow_0(A_363,k2_tarski(C_362,C_364))
      | ~ m1_subset_1(C_364,u1_struct_0(A_363))
      | ~ l1_orders_2(A_363) ) ),
    inference(resolution,[status(thm)],[c_743,c_4])).

tff(c_762,plain,(
    ! [A_93,C_105,B_101] :
      ( k1_yellow_0(A_93,k2_tarski(C_105,B_101)) = B_101
      | ~ r1_yellow_0(A_93,k2_tarski(C_105,B_101))
      | ~ r1_orders_2(A_93,B_101,B_101)
      | ~ r1_orders_2(A_93,C_105,B_101)
      | ~ m1_subset_1(C_105,u1_struct_0(A_93))
      | ~ m1_subset_1(B_101,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93) ) ),
    inference(resolution,[status(thm)],[c_48,c_757])).

tff(c_36007,plain,(
    ! [C_901] :
      ( k1_yellow_0('#skF_5',k2_tarski(C_901,k13_lattice3('#skF_5','#skF_7','#skF_6'))) = k13_lattice3('#skF_5','#skF_7','#skF_6')
      | ~ r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_7','#skF_6'))
      | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_orders_2('#skF_5',C_901,k13_lattice3('#skF_5','#skF_7','#skF_6'))
      | ~ m1_subset_1(C_901,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_36003,c_762])).

tff(c_36016,plain,(
    ! [C_901] :
      ( k1_yellow_0('#skF_5',k2_tarski(C_901,k13_lattice3('#skF_5','#skF_7','#skF_6'))) = k13_lattice3('#skF_5','#skF_7','#skF_6')
      | ~ r1_orders_2('#skF_5',C_901,k13_lattice3('#skF_5','#skF_7','#skF_6'))
      | ~ m1_subset_1(C_901,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32589,c_33650,c_36007])).

tff(c_249,plain,(
    ! [A_157,C_158,B_159,D_160] :
      ( r1_orders_2(A_157,C_158,B_159)
      | ~ r2_lattice3(A_157,k2_tarski(C_158,D_160),B_159)
      | ~ m1_subset_1(D_160,u1_struct_0(A_157))
      | ~ m1_subset_1(C_158,u1_struct_0(A_157))
      | ~ m1_subset_1(B_159,u1_struct_0(A_157))
      | ~ l1_orders_2(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_560,plain,(
    ! [A_277,C_278,D_279,C_280] :
      ( r1_orders_2(A_277,C_278,'#skF_2'(A_277,k2_tarski(C_278,D_279),C_280))
      | ~ m1_subset_1(D_279,u1_struct_0(A_277))
      | ~ m1_subset_1(C_278,u1_struct_0(A_277))
      | ~ m1_subset_1('#skF_2'(A_277,k2_tarski(C_278,D_279),C_280),u1_struct_0(A_277))
      | r1_yellow_0(A_277,k2_tarski(C_278,D_279))
      | ~ r2_lattice3(A_277,k2_tarski(C_278,D_279),C_280)
      | ~ m1_subset_1(C_280,u1_struct_0(A_277))
      | ~ l1_orders_2(A_277)
      | ~ v5_orders_2(A_277) ) ),
    inference(resolution,[status(thm)],[c_30,c_249])).

tff(c_565,plain,(
    ! [A_281,C_282,D_283,C_284] :
      ( r1_orders_2(A_281,C_282,'#skF_2'(A_281,k2_tarski(C_282,D_283),C_284))
      | ~ m1_subset_1(D_283,u1_struct_0(A_281))
      | ~ m1_subset_1(C_282,u1_struct_0(A_281))
      | r1_yellow_0(A_281,k2_tarski(C_282,D_283))
      | ~ r2_lattice3(A_281,k2_tarski(C_282,D_283),C_284)
      | ~ m1_subset_1(C_284,u1_struct_0(A_281))
      | ~ l1_orders_2(A_281)
      | ~ v5_orders_2(A_281) ) ),
    inference(resolution,[status(thm)],[c_32,c_560])).

tff(c_574,plain,(
    ! [D_285,A_286,C_287] :
      ( ~ m1_subset_1(D_285,u1_struct_0(A_286))
      | r1_yellow_0(A_286,k2_tarski(C_287,D_285))
      | ~ r2_lattice3(A_286,k2_tarski(C_287,D_285),C_287)
      | ~ m1_subset_1(C_287,u1_struct_0(A_286))
      | ~ l1_orders_2(A_286)
      | ~ v5_orders_2(A_286) ) ),
    inference(resolution,[status(thm)],[c_565,c_28])).

tff(c_579,plain,(
    ! [A_93,B_101,D_107] :
      ( r1_yellow_0(A_93,k2_tarski(B_101,D_107))
      | ~ v5_orders_2(A_93)
      | ~ r1_orders_2(A_93,D_107,B_101)
      | ~ r1_orders_2(A_93,B_101,B_101)
      | ~ m1_subset_1(D_107,u1_struct_0(A_93))
      | ~ m1_subset_1(B_101,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93) ) ),
    inference(resolution,[status(thm)],[c_48,c_574])).

tff(c_32867,plain,(
    ! [D_107] :
      ( r1_yellow_0('#skF_5',k2_tarski(k13_lattice3('#skF_5','#skF_6','#skF_7'),D_107))
      | ~ v5_orders_2('#skF_5')
      | ~ r1_orders_2('#skF_5',D_107,k13_lattice3('#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1(D_107,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32835,c_579])).

tff(c_35878,plain,(
    ! [D_900] :
      ( r1_yellow_0('#skF_5',k2_tarski(k13_lattice3('#skF_5','#skF_6','#skF_7'),D_900))
      | ~ r1_orders_2('#skF_5',D_900,k13_lattice3('#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1(D_900,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32158,c_70,c_32867])).

tff(c_278,plain,(
    ! [A_164,B_165,C_166] :
      ( r2_lattice3(A_164,B_165,'#skF_1'(A_164,B_165,C_166))
      | k1_yellow_0(A_164,B_165) = C_166
      | ~ r2_lattice3(A_164,B_165,C_166)
      | ~ r1_yellow_0(A_164,B_165)
      | ~ m1_subset_1(C_166,u1_struct_0(A_164))
      | ~ l1_orders_2(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_54,plain,(
    ! [A_93,C_105,B_101,D_107] :
      ( r1_orders_2(A_93,C_105,B_101)
      | ~ r2_lattice3(A_93,k2_tarski(C_105,D_107),B_101)
      | ~ m1_subset_1(D_107,u1_struct_0(A_93))
      | ~ m1_subset_1(C_105,u1_struct_0(A_93))
      | ~ m1_subset_1(B_101,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_752,plain,(
    ! [A_358,C_359,D_360,C_361] :
      ( r1_orders_2(A_358,C_359,'#skF_1'(A_358,k2_tarski(C_359,D_360),C_361))
      | ~ m1_subset_1(D_360,u1_struct_0(A_358))
      | ~ m1_subset_1(C_359,u1_struct_0(A_358))
      | ~ m1_subset_1('#skF_1'(A_358,k2_tarski(C_359,D_360),C_361),u1_struct_0(A_358))
      | k1_yellow_0(A_358,k2_tarski(C_359,D_360)) = C_361
      | ~ r2_lattice3(A_358,k2_tarski(C_359,D_360),C_361)
      | ~ r1_yellow_0(A_358,k2_tarski(C_359,D_360))
      | ~ m1_subset_1(C_361,u1_struct_0(A_358))
      | ~ l1_orders_2(A_358) ) ),
    inference(resolution,[status(thm)],[c_278,c_54])).

tff(c_770,plain,(
    ! [A_368,C_369,D_370,C_371] :
      ( r1_orders_2(A_368,C_369,'#skF_1'(A_368,k2_tarski(C_369,D_370),C_371))
      | ~ m1_subset_1(D_370,u1_struct_0(A_368))
      | ~ m1_subset_1(C_369,u1_struct_0(A_368))
      | k1_yellow_0(A_368,k2_tarski(C_369,D_370)) = C_371
      | ~ r2_lattice3(A_368,k2_tarski(C_369,D_370),C_371)
      | ~ r1_yellow_0(A_368,k2_tarski(C_369,D_370))
      | ~ m1_subset_1(C_371,u1_struct_0(A_368))
      | ~ l1_orders_2(A_368) ) ),
    inference(resolution,[status(thm)],[c_8,c_752])).

tff(c_779,plain,(
    ! [D_372,A_373,C_374] :
      ( ~ m1_subset_1(D_372,u1_struct_0(A_373))
      | k1_yellow_0(A_373,k2_tarski(C_374,D_372)) = C_374
      | ~ r2_lattice3(A_373,k2_tarski(C_374,D_372),C_374)
      | ~ r1_yellow_0(A_373,k2_tarski(C_374,D_372))
      | ~ m1_subset_1(C_374,u1_struct_0(A_373))
      | ~ l1_orders_2(A_373) ) ),
    inference(resolution,[status(thm)],[c_770,c_4])).

tff(c_784,plain,(
    ! [A_93,B_101,D_107] :
      ( k1_yellow_0(A_93,k2_tarski(B_101,D_107)) = B_101
      | ~ r1_yellow_0(A_93,k2_tarski(B_101,D_107))
      | ~ r1_orders_2(A_93,D_107,B_101)
      | ~ r1_orders_2(A_93,B_101,B_101)
      | ~ m1_subset_1(D_107,u1_struct_0(A_93))
      | ~ m1_subset_1(B_101,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93) ) ),
    inference(resolution,[status(thm)],[c_48,c_779])).

tff(c_35880,plain,(
    ! [D_900] :
      ( k1_yellow_0('#skF_5',k2_tarski(k13_lattice3('#skF_5','#skF_6','#skF_7'),D_900)) = k13_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_orders_2('#skF_5',D_900,k13_lattice3('#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1(D_900,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_35878,c_784])).

tff(c_43430,plain,(
    ! [D_955] :
      ( k1_yellow_0('#skF_5',k2_tarski(k13_lattice3('#skF_5','#skF_6','#skF_7'),D_955)) = k13_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ r1_orders_2('#skF_5',D_955,k13_lattice3('#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1(D_955,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32158,c_32835,c_35880])).

tff(c_43480,plain,
    ( k13_lattice3('#skF_5','#skF_7','#skF_6') = k13_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36016,c_43430])).

tff(c_43604,plain,
    ( k13_lattice3('#skF_5','#skF_7','#skF_6') = k13_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32158,c_32589,c_43480])).

tff(c_53988,plain,(
    ~ r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_43604])).

tff(c_53991,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7',k13_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ r1_orders_2('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_490,c_53988])).

tff(c_53995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_32589,c_34039,c_32588,c_53991])).

tff(c_53996,plain,
    ( ~ r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | k13_lattice3('#skF_5','#skF_7','#skF_6') = k13_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_43604])).

tff(c_54806,plain,(
    ~ r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_53996])).

tff(c_54809,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_orders_2('#skF_5','#skF_7',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_490,c_54806])).

tff(c_54813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_62,c_64,c_32158,c_33224,c_32157,c_54809])).

tff(c_54814,plain,(
    k13_lattice3('#skF_5','#skF_7','#skF_6') = k13_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_53996])).

tff(c_670,plain,(
    ! [A_2,D_331,C_332,C_10] :
      ( r1_orders_2(A_2,D_331,'#skF_1'(A_2,k2_tarski(C_332,D_331),C_10))
      | ~ m1_subset_1(D_331,u1_struct_0(A_2))
      | ~ m1_subset_1(C_332,u1_struct_0(A_2))
      | k1_yellow_0(A_2,k2_tarski(C_332,D_331)) = C_10
      | ~ r2_lattice3(A_2,k2_tarski(C_332,D_331),C_10)
      | ~ r1_yellow_0(A_2,k2_tarski(C_332,D_331))
      | ~ m1_subset_1(C_10,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(resolution,[status(thm)],[c_8,c_666])).

tff(c_756,plain,(
    ! [A_2,C_359,D_360,C_10] :
      ( r1_orders_2(A_2,C_359,'#skF_1'(A_2,k2_tarski(C_359,D_360),C_10))
      | ~ m1_subset_1(D_360,u1_struct_0(A_2))
      | ~ m1_subset_1(C_359,u1_struct_0(A_2))
      | k1_yellow_0(A_2,k2_tarski(C_359,D_360)) = C_10
      | ~ r2_lattice3(A_2,k2_tarski(C_359,D_360),C_10)
      | ~ r1_yellow_0(A_2,k2_tarski(C_359,D_360))
      | ~ m1_subset_1(C_10,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(resolution,[status(thm)],[c_8,c_752])).

tff(c_2567,plain,(
    ! [A_464,B_465,B_466,C_467] :
      ( k1_yellow_0(A_464,B_465) = k13_lattice3(A_464,B_466,C_467)
      | ~ r2_lattice3(A_464,B_465,k13_lattice3(A_464,B_466,C_467))
      | ~ r1_yellow_0(A_464,B_465)
      | ~ m1_subset_1(k13_lattice3(A_464,B_466,C_467),u1_struct_0(A_464))
      | ~ r1_orders_2(A_464,C_467,'#skF_1'(A_464,B_465,k13_lattice3(A_464,B_466,C_467)))
      | ~ r1_orders_2(A_464,B_466,'#skF_1'(A_464,B_465,k13_lattice3(A_464,B_466,C_467)))
      | ~ m1_subset_1('#skF_1'(A_464,B_465,k13_lattice3(A_464,B_466,C_467)),u1_struct_0(A_464))
      | ~ m1_subset_1(C_467,u1_struct_0(A_464))
      | ~ m1_subset_1(B_466,u1_struct_0(A_464))
      | ~ l1_orders_2(A_464)
      | ~ v1_lattice3(A_464)
      | ~ v5_orders_2(A_464) ) ),
    inference(resolution,[status(thm)],[c_491,c_4])).

tff(c_12449,plain,(
    ! [A_633,B_634,C_635,D_636] :
      ( ~ r1_orders_2(A_633,B_634,'#skF_1'(A_633,k2_tarski(C_635,D_636),k13_lattice3(A_633,B_634,C_635)))
      | ~ m1_subset_1('#skF_1'(A_633,k2_tarski(C_635,D_636),k13_lattice3(A_633,B_634,C_635)),u1_struct_0(A_633))
      | ~ m1_subset_1(B_634,u1_struct_0(A_633))
      | ~ v1_lattice3(A_633)
      | ~ v5_orders_2(A_633)
      | ~ m1_subset_1(D_636,u1_struct_0(A_633))
      | ~ m1_subset_1(C_635,u1_struct_0(A_633))
      | k1_yellow_0(A_633,k2_tarski(C_635,D_636)) = k13_lattice3(A_633,B_634,C_635)
      | ~ r2_lattice3(A_633,k2_tarski(C_635,D_636),k13_lattice3(A_633,B_634,C_635))
      | ~ r1_yellow_0(A_633,k2_tarski(C_635,D_636))
      | ~ m1_subset_1(k13_lattice3(A_633,B_634,C_635),u1_struct_0(A_633))
      | ~ l1_orders_2(A_633) ) ),
    inference(resolution,[status(thm)],[c_756,c_2567])).

tff(c_12531,plain,(
    ! [A_2,C_332,D_331] :
      ( ~ m1_subset_1('#skF_1'(A_2,k2_tarski(C_332,D_331),k13_lattice3(A_2,D_331,C_332)),u1_struct_0(A_2))
      | ~ v1_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | ~ m1_subset_1(D_331,u1_struct_0(A_2))
      | ~ m1_subset_1(C_332,u1_struct_0(A_2))
      | k1_yellow_0(A_2,k2_tarski(C_332,D_331)) = k13_lattice3(A_2,D_331,C_332)
      | ~ r2_lattice3(A_2,k2_tarski(C_332,D_331),k13_lattice3(A_2,D_331,C_332))
      | ~ r1_yellow_0(A_2,k2_tarski(C_332,D_331))
      | ~ m1_subset_1(k13_lattice3(A_2,D_331,C_332),u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(resolution,[status(thm)],[c_670,c_12449])).

tff(c_54908,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | k1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) = k13_lattice3('#skF_5','#skF_7','#skF_6')
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_54814,c_12531])).

tff(c_55010,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | k1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) = k13_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32158,c_54814,c_54814,c_54814,c_64,c_62,c_70,c_68,c_54908])).

tff(c_55011,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_55010])).

tff(c_70895,plain,(
    ~ r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_55011])).

tff(c_56604,plain,(
    ~ r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_55011])).

tff(c_564,plain,(
    ! [A_22,C_278,D_279,C_43] :
      ( r1_orders_2(A_22,C_278,'#skF_2'(A_22,k2_tarski(C_278,D_279),C_43))
      | ~ m1_subset_1(D_279,u1_struct_0(A_22))
      | ~ m1_subset_1(C_278,u1_struct_0(A_22))
      | r1_yellow_0(A_22,k2_tarski(C_278,D_279))
      | ~ r2_lattice3(A_22,k2_tarski(C_278,D_279),C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(resolution,[status(thm)],[c_32,c_560])).

tff(c_602,plain,(
    ! [A_22,D_298,C_299,C_43] :
      ( r1_orders_2(A_22,D_298,'#skF_2'(A_22,k2_tarski(C_299,D_298),C_43))
      | ~ m1_subset_1(D_298,u1_struct_0(A_22))
      | ~ m1_subset_1(C_299,u1_struct_0(A_22))
      | r1_yellow_0(A_22,k2_tarski(C_299,D_298))
      | ~ r2_lattice3(A_22,k2_tarski(C_299,D_298),C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(resolution,[status(thm)],[c_32,c_598])).

tff(c_1831,plain,(
    ! [A_444,B_445,B_446,C_447] :
      ( r1_yellow_0(A_444,B_445)
      | ~ r2_lattice3(A_444,B_445,k13_lattice3(A_444,B_446,C_447))
      | ~ m1_subset_1(k13_lattice3(A_444,B_446,C_447),u1_struct_0(A_444))
      | ~ r1_orders_2(A_444,C_447,'#skF_2'(A_444,B_445,k13_lattice3(A_444,B_446,C_447)))
      | ~ r1_orders_2(A_444,B_446,'#skF_2'(A_444,B_445,k13_lattice3(A_444,B_446,C_447)))
      | ~ m1_subset_1('#skF_2'(A_444,B_445,k13_lattice3(A_444,B_446,C_447)),u1_struct_0(A_444))
      | ~ m1_subset_1(C_447,u1_struct_0(A_444))
      | ~ m1_subset_1(B_446,u1_struct_0(A_444))
      | ~ l1_orders_2(A_444)
      | ~ v1_lattice3(A_444)
      | ~ v5_orders_2(A_444) ) ),
    inference(resolution,[status(thm)],[c_491,c_28])).

tff(c_8039,plain,(
    ! [A_575,B_576,C_577,D_578] :
      ( ~ r1_orders_2(A_575,B_576,'#skF_2'(A_575,k2_tarski(C_577,D_578),k13_lattice3(A_575,B_576,D_578)))
      | ~ m1_subset_1('#skF_2'(A_575,k2_tarski(C_577,D_578),k13_lattice3(A_575,B_576,D_578)),u1_struct_0(A_575))
      | ~ m1_subset_1(B_576,u1_struct_0(A_575))
      | ~ v1_lattice3(A_575)
      | ~ m1_subset_1(D_578,u1_struct_0(A_575))
      | ~ m1_subset_1(C_577,u1_struct_0(A_575))
      | r1_yellow_0(A_575,k2_tarski(C_577,D_578))
      | ~ r2_lattice3(A_575,k2_tarski(C_577,D_578),k13_lattice3(A_575,B_576,D_578))
      | ~ m1_subset_1(k13_lattice3(A_575,B_576,D_578),u1_struct_0(A_575))
      | ~ l1_orders_2(A_575)
      | ~ v5_orders_2(A_575) ) ),
    inference(resolution,[status(thm)],[c_602,c_1831])).

tff(c_8123,plain,(
    ! [A_22,C_278,D_279] :
      ( ~ m1_subset_1('#skF_2'(A_22,k2_tarski(C_278,D_279),k13_lattice3(A_22,C_278,D_279)),u1_struct_0(A_22))
      | ~ v1_lattice3(A_22)
      | ~ m1_subset_1(D_279,u1_struct_0(A_22))
      | ~ m1_subset_1(C_278,u1_struct_0(A_22))
      | r1_yellow_0(A_22,k2_tarski(C_278,D_279))
      | ~ r2_lattice3(A_22,k2_tarski(C_278,D_279),k13_lattice3(A_22,C_278,D_279))
      | ~ m1_subset_1(k13_lattice3(A_22,C_278,D_279),u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(resolution,[status(thm)],[c_564,c_8039])).

tff(c_54917,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ v1_lattice3('#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_7','#skF_6'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_54814,c_8123])).

tff(c_55017,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_32158,c_54814,c_54814,c_62,c_64,c_68,c_54917])).

tff(c_55718,plain,(
    ~ r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_55017])).

tff(c_55722,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_orders_2('#skF_5','#skF_7',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_55718])).

tff(c_55726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32158,c_62,c_64,c_33224,c_32157,c_55722])).

tff(c_55728,plain,(
    r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_55017])).

tff(c_55727,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_55017])).

tff(c_55741,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_55727])).

tff(c_55744,plain,
    ( r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_55741])).

tff(c_55747,plain,(
    r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_32158,c_55728,c_55744])).

tff(c_26,plain,(
    ! [A_22,B_36] :
      ( m1_subset_1('#skF_3'(A_22,B_36),u1_struct_0(A_22))
      | ~ r1_yellow_0(A_22,B_36)
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24,plain,(
    ! [A_22,B_36] :
      ( r2_lattice3(A_22,B_36,'#skF_3'(A_22,B_36))
      | ~ r1_yellow_0(A_22,B_36)
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22,plain,(
    ! [A_22,B_36,D_46] :
      ( r1_orders_2(A_22,'#skF_3'(A_22,B_36),D_46)
      | ~ r2_lattice3(A_22,B_36,D_46)
      | ~ m1_subset_1(D_46,u1_struct_0(A_22))
      | ~ r1_yellow_0(A_22,B_36)
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_284,plain,(
    ! [A_167,C_168,B_169] :
      ( ~ r1_orders_2(A_167,C_168,'#skF_1'(A_167,B_169,C_168))
      | k1_yellow_0(A_167,B_169) = C_168
      | ~ r2_lattice3(A_167,B_169,C_168)
      | ~ r1_yellow_0(A_167,B_169)
      | ~ m1_subset_1(C_168,u1_struct_0(A_167))
      | ~ l1_orders_2(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_657,plain,(
    ! [A_327,B_328,B_329] :
      ( k1_yellow_0(A_327,B_328) = '#skF_3'(A_327,B_329)
      | ~ r2_lattice3(A_327,B_328,'#skF_3'(A_327,B_329))
      | ~ r1_yellow_0(A_327,B_328)
      | ~ m1_subset_1('#skF_3'(A_327,B_329),u1_struct_0(A_327))
      | ~ r2_lattice3(A_327,B_329,'#skF_1'(A_327,B_328,'#skF_3'(A_327,B_329)))
      | ~ m1_subset_1('#skF_1'(A_327,B_328,'#skF_3'(A_327,B_329)),u1_struct_0(A_327))
      | ~ r1_yellow_0(A_327,B_329)
      | ~ l1_orders_2(A_327)
      | ~ v5_orders_2(A_327) ) ),
    inference(resolution,[status(thm)],[c_22,c_284])).

tff(c_671,plain,(
    ! [A_334,B_335] :
      ( ~ m1_subset_1('#skF_1'(A_334,B_335,'#skF_3'(A_334,B_335)),u1_struct_0(A_334))
      | ~ v5_orders_2(A_334)
      | k1_yellow_0(A_334,B_335) = '#skF_3'(A_334,B_335)
      | ~ r2_lattice3(A_334,B_335,'#skF_3'(A_334,B_335))
      | ~ r1_yellow_0(A_334,B_335)
      | ~ m1_subset_1('#skF_3'(A_334,B_335),u1_struct_0(A_334))
      | ~ l1_orders_2(A_334) ) ),
    inference(resolution,[status(thm)],[c_6,c_657])).

tff(c_677,plain,(
    ! [A_336,B_337] :
      ( ~ v5_orders_2(A_336)
      | k1_yellow_0(A_336,B_337) = '#skF_3'(A_336,B_337)
      | ~ r2_lattice3(A_336,B_337,'#skF_3'(A_336,B_337))
      | ~ r1_yellow_0(A_336,B_337)
      | ~ m1_subset_1('#skF_3'(A_336,B_337),u1_struct_0(A_336))
      | ~ l1_orders_2(A_336) ) ),
    inference(resolution,[status(thm)],[c_8,c_671])).

tff(c_685,plain,(
    ! [A_338,B_339] :
      ( k1_yellow_0(A_338,B_339) = '#skF_3'(A_338,B_339)
      | ~ m1_subset_1('#skF_3'(A_338,B_339),u1_struct_0(A_338))
      | ~ r1_yellow_0(A_338,B_339)
      | ~ l1_orders_2(A_338)
      | ~ v5_orders_2(A_338) ) ),
    inference(resolution,[status(thm)],[c_24,c_677])).

tff(c_689,plain,(
    ! [A_22,B_36] :
      ( k1_yellow_0(A_22,B_36) = '#skF_3'(A_22,B_36)
      | ~ r1_yellow_0(A_22,B_36)
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(resolution,[status(thm)],[c_26,c_685])).

tff(c_55945,plain,
    ( k1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6')) = '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_55747,c_689])).

tff(c_55954,plain,(
    k1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6')) = '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_55945])).

tff(c_12,plain,(
    ! [A_2,B_9] :
      ( r2_lattice3(A_2,B_9,k1_yellow_0(A_2,B_9))
      | ~ r1_yellow_0(A_2,B_9)
      | ~ m1_subset_1(k1_yellow_0(A_2,B_9),u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_55959,plain,
    ( r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_6'),k1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_55954,c_12])).

tff(c_55965,plain,
    ( r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_6'),'#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_55747,c_55954,c_55959])).

tff(c_55967,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_55965])).

tff(c_55971,plain,
    ( ~ r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_55967])).

tff(c_55975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_55747,c_55971])).

tff(c_55977,plain,(
    m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_55965])).

tff(c_55976,plain,(
    r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_6'),'#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_55965])).

tff(c_56061,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_55976,c_54])).

tff(c_56085,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_55977,c_62,c_64,c_56061])).

tff(c_52,plain,(
    ! [A_93,D_107,B_101,C_105] :
      ( r1_orders_2(A_93,D_107,B_101)
      | ~ r2_lattice3(A_93,k2_tarski(C_105,D_107),B_101)
      | ~ m1_subset_1(D_107,u1_struct_0(A_93))
      | ~ m1_subset_1(C_105,u1_struct_0(A_93))
      | ~ m1_subset_1(B_101,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_56058,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_55976,c_52])).

tff(c_56082,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_55977,c_62,c_64,c_56058])).

tff(c_381,plain,(
    ! [A_212,C_213,D_214] :
      ( r1_orders_2(A_212,C_213,'#skF_3'(A_212,k2_tarski(C_213,D_214)))
      | ~ m1_subset_1(D_214,u1_struct_0(A_212))
      | ~ m1_subset_1(C_213,u1_struct_0(A_212))
      | ~ m1_subset_1('#skF_3'(A_212,k2_tarski(C_213,D_214)),u1_struct_0(A_212))
      | ~ r1_yellow_0(A_212,k2_tarski(C_213,D_214))
      | ~ l1_orders_2(A_212)
      | ~ v5_orders_2(A_212) ) ),
    inference(resolution,[status(thm)],[c_24,c_249])).

tff(c_385,plain,(
    ! [A_22,C_213,D_214] :
      ( r1_orders_2(A_22,C_213,'#skF_3'(A_22,k2_tarski(C_213,D_214)))
      | ~ m1_subset_1(D_214,u1_struct_0(A_22))
      | ~ m1_subset_1(C_213,u1_struct_0(A_22))
      | ~ r1_yellow_0(A_22,k2_tarski(C_213,D_214))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(resolution,[status(thm)],[c_26,c_381])).

tff(c_6699,plain,(
    ! [A_551,C_552,D_553] :
      ( k13_lattice3(A_551,'#skF_3'(A_551,k2_tarski(C_552,D_553)),C_552) = '#skF_3'(A_551,k2_tarski(C_552,D_553))
      | ~ r1_orders_2(A_551,'#skF_3'(A_551,k2_tarski(C_552,D_553)),'#skF_3'(A_551,k2_tarski(C_552,D_553)))
      | ~ m1_subset_1('#skF_3'(A_551,k2_tarski(C_552,D_553)),u1_struct_0(A_551))
      | ~ v1_lattice3(A_551)
      | ~ m1_subset_1(D_553,u1_struct_0(A_551))
      | ~ m1_subset_1(C_552,u1_struct_0(A_551))
      | ~ r1_yellow_0(A_551,k2_tarski(C_552,D_553))
      | ~ l1_orders_2(A_551)
      | ~ v5_orders_2(A_551) ) ),
    inference(resolution,[status(thm)],[c_385,c_442])).

tff(c_6804,plain,(
    ! [A_22,C_552,D_553] :
      ( k13_lattice3(A_22,'#skF_3'(A_22,k2_tarski(C_552,D_553)),C_552) = '#skF_3'(A_22,k2_tarski(C_552,D_553))
      | ~ v1_lattice3(A_22)
      | ~ m1_subset_1(D_553,u1_struct_0(A_22))
      | ~ m1_subset_1(C_552,u1_struct_0(A_22))
      | ~ r2_lattice3(A_22,k2_tarski(C_552,D_553),'#skF_3'(A_22,k2_tarski(C_552,D_553)))
      | ~ m1_subset_1('#skF_3'(A_22,k2_tarski(C_552,D_553)),u1_struct_0(A_22))
      | ~ r1_yellow_0(A_22,k2_tarski(C_552,D_553))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(resolution,[status(thm)],[c_22,c_6699])).

tff(c_56051,plain,
    ( k13_lattice3('#skF_5','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),'#skF_7') = '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ v1_lattice3('#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_55976,c_6804])).

tff(c_56073,plain,(
    k13_lattice3('#skF_5','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),'#skF_7') = '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_55747,c_55977,c_62,c_64,c_68,c_56051])).

tff(c_56398,plain,
    ( r1_orders_2('#skF_5','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),'#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_56073,c_351])).

tff(c_56497,plain,(
    r1_orders_2('#skF_5','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),'#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_55977,c_62,c_56398])).

tff(c_54970,plain,(
    ! [E_260] :
      ( r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_6','#skF_7'),E_260)
      | ~ r1_orders_2('#skF_5','#skF_6',E_260)
      | ~ r1_orders_2('#skF_5','#skF_7',E_260)
      | ~ m1_subset_1(E_260,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_lattice3('#skF_5')
      | ~ v5_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54814,c_490])).

tff(c_55236,plain,(
    ! [E_1041] :
      ( r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_6','#skF_7'),E_1041)
      | ~ r1_orders_2('#skF_5','#skF_6',E_1041)
      | ~ r1_orders_2('#skF_5','#skF_7',E_1041)
      | ~ m1_subset_1(E_1041,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_62,c_64,c_54970])).

tff(c_441,plain,(
    ! [A_243,D_246,C_245] :
      ( k13_lattice3(A_243,D_246,C_245) = D_246
      | ~ r1_orders_2(A_243,C_245,D_246)
      | ~ r1_orders_2(A_243,D_246,D_246)
      | ~ m1_subset_1(C_245,u1_struct_0(A_243))
      | ~ m1_subset_1(D_246,u1_struct_0(A_243))
      | ~ l1_orders_2(A_243)
      | ~ v1_lattice3(A_243)
      | ~ v5_orders_2(A_243) ) ),
    inference(resolution,[status(thm)],[c_436,c_34])).

tff(c_55436,plain,(
    ! [E_1041] :
      ( k13_lattice3('#skF_5',E_1041,k13_lattice3('#skF_5','#skF_6','#skF_7')) = E_1041
      | ~ r1_orders_2('#skF_5',E_1041,E_1041)
      | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_lattice3('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ r1_orders_2('#skF_5','#skF_6',E_1041)
      | ~ r1_orders_2('#skF_5','#skF_7',E_1041)
      | ~ m1_subset_1(E_1041,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_55236,c_441])).

tff(c_55643,plain,(
    ! [E_1041] :
      ( k13_lattice3('#skF_5',E_1041,k13_lattice3('#skF_5','#skF_6','#skF_7')) = E_1041
      | ~ r1_orders_2('#skF_5',E_1041,E_1041)
      | ~ r1_orders_2('#skF_5','#skF_6',E_1041)
      | ~ r1_orders_2('#skF_5','#skF_7',E_1041)
      | ~ m1_subset_1(E_1041,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_32158,c_55436])).

tff(c_56508,plain,
    ( k13_lattice3('#skF_5','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),k13_lattice3('#skF_5','#skF_6','#skF_7')) = '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_56497,c_55643])).

tff(c_56549,plain,(
    k13_lattice3('#skF_5','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),k13_lattice3('#skF_5','#skF_6','#skF_7')) = '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55977,c_56085,c_56082,c_56508])).

tff(c_8718,plain,(
    ! [A_583,B_584,B_585,C_586] :
      ( k13_lattice3(A_583,'#skF_3'(A_583,B_584),k13_lattice3(A_583,B_585,C_586)) = k13_lattice3(A_583,B_585,C_586)
      | ~ m1_subset_1('#skF_3'(A_583,B_584),u1_struct_0(A_583))
      | ~ r1_orders_2(A_583,C_586,k13_lattice3(A_583,B_585,C_586))
      | ~ r1_orders_2(A_583,B_585,k13_lattice3(A_583,B_585,C_586))
      | ~ m1_subset_1(C_586,u1_struct_0(A_583))
      | ~ m1_subset_1(B_585,u1_struct_0(A_583))
      | ~ v1_lattice3(A_583)
      | ~ r2_lattice3(A_583,B_584,k13_lattice3(A_583,B_585,C_586))
      | ~ m1_subset_1(k13_lattice3(A_583,B_585,C_586),u1_struct_0(A_583))
      | ~ r1_yellow_0(A_583,B_584)
      | ~ l1_orders_2(A_583)
      | ~ v5_orders_2(A_583) ) ),
    inference(resolution,[status(thm)],[c_22,c_1626])).

tff(c_45259,plain,(
    ! [A_975,B_976,B_977,C_978] :
      ( k13_lattice3(A_975,'#skF_3'(A_975,B_976),k13_lattice3(A_975,B_977,C_978)) = k13_lattice3(A_975,B_977,C_978)
      | ~ r1_orders_2(A_975,C_978,k13_lattice3(A_975,B_977,C_978))
      | ~ r1_orders_2(A_975,B_977,k13_lattice3(A_975,B_977,C_978))
      | ~ m1_subset_1(C_978,u1_struct_0(A_975))
      | ~ m1_subset_1(B_977,u1_struct_0(A_975))
      | ~ v1_lattice3(A_975)
      | ~ r2_lattice3(A_975,B_976,k13_lattice3(A_975,B_977,C_978))
      | ~ m1_subset_1(k13_lattice3(A_975,B_977,C_978),u1_struct_0(A_975))
      | ~ r1_yellow_0(A_975,B_976)
      | ~ l1_orders_2(A_975)
      | ~ v5_orders_2(A_975) ) ),
    inference(resolution,[status(thm)],[c_26,c_8718])).

tff(c_45355,plain,(
    ! [B_976] :
      ( k13_lattice3('#skF_5','#skF_3'('#skF_5',B_976),k13_lattice3('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7'))) = k13_lattice3('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7'))
      | ~ r1_orders_2('#skF_5',k13_lattice3('#skF_5','#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
      | ~ r1_orders_2('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7')))
      | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ v1_lattice3('#skF_5')
      | ~ r2_lattice3('#skF_5',B_976,k13_lattice3('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7')))
      | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',B_976)
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31984,c_45259])).

tff(c_45512,plain,(
    ! [B_976] :
      ( k13_lattice3('#skF_5','#skF_3'('#skF_5',B_976),k13_lattice3('#skF_5','#skF_6','#skF_7')) = k13_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ r2_lattice3('#skF_5',B_976,k13_lattice3('#skF_5','#skF_6','#skF_7'))
      | ~ r1_yellow_0('#skF_5',B_976) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_32158,c_31984,c_31984,c_68,c_64,c_32158,c_32157,c_31984,c_32835,c_31984,c_31984,c_45355])).

tff(c_57533,plain,
    ( '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')) = k13_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56549,c_45512])).

tff(c_57658,plain,(
    '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')) = k13_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55747,c_55728,c_57533])).

tff(c_222,plain,(
    ! [A_139,C_140,B_141] :
      ( ~ r1_orders_2(A_139,C_140,'#skF_2'(A_139,B_141,C_140))
      | r1_yellow_0(A_139,B_141)
      | ~ r2_lattice3(A_139,B_141,C_140)
      | ~ m1_subset_1(C_140,u1_struct_0(A_139))
      | ~ l1_orders_2(A_139)
      | ~ v5_orders_2(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_518,plain,(
    ! [A_265,B_266,B_267] :
      ( r1_yellow_0(A_265,B_266)
      | ~ r2_lattice3(A_265,B_266,'#skF_3'(A_265,B_267))
      | ~ m1_subset_1('#skF_3'(A_265,B_267),u1_struct_0(A_265))
      | ~ r2_lattice3(A_265,B_267,'#skF_2'(A_265,B_266,'#skF_3'(A_265,B_267)))
      | ~ m1_subset_1('#skF_2'(A_265,B_266,'#skF_3'(A_265,B_267)),u1_struct_0(A_265))
      | ~ r1_yellow_0(A_265,B_267)
      | ~ l1_orders_2(A_265)
      | ~ v5_orders_2(A_265) ) ),
    inference(resolution,[status(thm)],[c_22,c_222])).

tff(c_2828,plain,(
    ! [A_472,B_473,C_474,D_475] :
      ( r1_yellow_0(A_472,B_473)
      | ~ r2_lattice3(A_472,B_473,'#skF_3'(A_472,k2_tarski(C_474,D_475)))
      | ~ m1_subset_1('#skF_3'(A_472,k2_tarski(C_474,D_475)),u1_struct_0(A_472))
      | ~ r1_yellow_0(A_472,k2_tarski(C_474,D_475))
      | ~ v5_orders_2(A_472)
      | ~ r1_orders_2(A_472,D_475,'#skF_2'(A_472,B_473,'#skF_3'(A_472,k2_tarski(C_474,D_475))))
      | ~ r1_orders_2(A_472,C_474,'#skF_2'(A_472,B_473,'#skF_3'(A_472,k2_tarski(C_474,D_475))))
      | ~ m1_subset_1(D_475,u1_struct_0(A_472))
      | ~ m1_subset_1(C_474,u1_struct_0(A_472))
      | ~ m1_subset_1('#skF_2'(A_472,B_473,'#skF_3'(A_472,k2_tarski(C_474,D_475))),u1_struct_0(A_472))
      | ~ l1_orders_2(A_472) ) ),
    inference(resolution,[status(thm)],[c_48,c_518])).

tff(c_12304,plain,(
    ! [A_627,C_628,C_629,D_630] :
      ( ~ r1_yellow_0(A_627,k2_tarski(C_628,C_629))
      | ~ r1_orders_2(A_627,C_628,'#skF_2'(A_627,k2_tarski(C_629,D_630),'#skF_3'(A_627,k2_tarski(C_628,C_629))))
      | ~ m1_subset_1(C_628,u1_struct_0(A_627))
      | ~ m1_subset_1('#skF_2'(A_627,k2_tarski(C_629,D_630),'#skF_3'(A_627,k2_tarski(C_628,C_629))),u1_struct_0(A_627))
      | ~ m1_subset_1(D_630,u1_struct_0(A_627))
      | ~ m1_subset_1(C_629,u1_struct_0(A_627))
      | r1_yellow_0(A_627,k2_tarski(C_629,D_630))
      | ~ r2_lattice3(A_627,k2_tarski(C_629,D_630),'#skF_3'(A_627,k2_tarski(C_628,C_629)))
      | ~ m1_subset_1('#skF_3'(A_627,k2_tarski(C_628,C_629)),u1_struct_0(A_627))
      | ~ l1_orders_2(A_627)
      | ~ v5_orders_2(A_627) ) ),
    inference(resolution,[status(thm)],[c_564,c_2828])).

tff(c_12395,plain,(
    ! [A_22,D_298,C_299] :
      ( ~ r1_yellow_0(A_22,k2_tarski(D_298,C_299))
      | ~ m1_subset_1('#skF_2'(A_22,k2_tarski(C_299,D_298),'#skF_3'(A_22,k2_tarski(D_298,C_299))),u1_struct_0(A_22))
      | ~ m1_subset_1(D_298,u1_struct_0(A_22))
      | ~ m1_subset_1(C_299,u1_struct_0(A_22))
      | r1_yellow_0(A_22,k2_tarski(C_299,D_298))
      | ~ r2_lattice3(A_22,k2_tarski(C_299,D_298),'#skF_3'(A_22,k2_tarski(D_298,C_299)))
      | ~ m1_subset_1('#skF_3'(A_22,k2_tarski(D_298,C_299)),u1_struct_0(A_22))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(resolution,[status(thm)],[c_602,c_12304])).

tff(c_57807,plain,
    ( ~ r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),'#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_57658,c_12395])).

tff(c_58168,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_32158,c_57658,c_57658,c_64,c_62,c_55747,c_57807])).

tff(c_58169,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_56604,c_58168])).

tff(c_67869,plain,(
    ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_58169])).

tff(c_67872,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_orders_2('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_67869])).

tff(c_67876,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32158,c_64,c_62,c_32157,c_33224,c_67872])).

tff(c_67878,plain,(
    r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_58169])).

tff(c_67877,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_58169])).

tff(c_67893,plain,
    ( r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_67877])).

tff(c_67896,plain,(
    r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_32158,c_67878,c_67893])).

tff(c_67898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56604,c_67896])).

tff(c_67900,plain,(
    r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_55011])).

tff(c_67907,plain,
    ( k1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) = '#skF_3'('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_67900,c_689])).

tff(c_67916,plain,(
    k1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) = '#skF_3'('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_67907])).

tff(c_68072,plain,(
    '#skF_3'('#skF_5',k2_tarski('#skF_6','#skF_7')) != k13_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67916,c_137])).

tff(c_67899,plain,
    ( ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_55011])).

tff(c_70600,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_67899])).

tff(c_70603,plain,
    ( k1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) = k13_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_70600])).

tff(c_70606,plain,
    ( '#skF_3'('#skF_5',k2_tarski('#skF_6','#skF_7')) = k13_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32158,c_67900,c_67916,c_70603])).

tff(c_70607,plain,(
    ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_68072,c_70606])).

tff(c_70610,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_orders_2('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_70607])).

tff(c_70614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32158,c_64,c_62,c_32157,c_33224,c_70610])).

tff(c_70615,plain,(
    ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_67899])).

tff(c_70619,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_orders_2('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_70615])).

tff(c_70623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32158,c_64,c_62,c_32157,c_33224,c_70619])).

tff(c_70624,plain,(
    r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_55727])).

tff(c_70632,plain,
    ( k1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6')) = '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_70624,c_689])).

tff(c_70641,plain,(
    k1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6')) = '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_70632])).

tff(c_70646,plain,
    ( r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_6'),k1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_70641,c_12])).

tff(c_70652,plain,
    ( r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_6'),'#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70624,c_70641,c_70646])).

tff(c_70885,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_70652])).

tff(c_70888,plain,
    ( ~ r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_70885])).

tff(c_70892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_70624,c_70888])).

tff(c_70894,plain,(
    m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_70652])).

tff(c_70893,plain,(
    r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_6'),'#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_70652])).

tff(c_70979,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_70893,c_54])).

tff(c_71003,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70894,c_62,c_64,c_70979])).

tff(c_70976,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_70893,c_52])).

tff(c_71000,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70894,c_62,c_64,c_70976])).

tff(c_413,plain,(
    ! [A_232,B_233,D_234] :
      ( k13_lattice3(A_232,B_233,D_234) = D_234
      | ~ r1_orders_2(A_232,D_234,D_234)
      | ~ r1_orders_2(A_232,B_233,D_234)
      | ~ m1_subset_1(D_234,u1_struct_0(A_232))
      | ~ m1_subset_1(B_233,u1_struct_0(A_232))
      | ~ l1_orders_2(A_232)
      | ~ v1_lattice3(A_232)
      | ~ v5_orders_2(A_232) ) ),
    inference(resolution,[status(thm)],[c_36,c_402])).

tff(c_527,plain,(
    ! [A_268,B_269,B_270] :
      ( k13_lattice3(A_268,B_269,'#skF_3'(A_268,B_270)) = '#skF_3'(A_268,B_270)
      | ~ r1_orders_2(A_268,B_269,'#skF_3'(A_268,B_270))
      | ~ m1_subset_1(B_269,u1_struct_0(A_268))
      | ~ v1_lattice3(A_268)
      | ~ r2_lattice3(A_268,B_270,'#skF_3'(A_268,B_270))
      | ~ m1_subset_1('#skF_3'(A_268,B_270),u1_struct_0(A_268))
      | ~ r1_yellow_0(A_268,B_270)
      | ~ l1_orders_2(A_268)
      | ~ v5_orders_2(A_268) ) ),
    inference(resolution,[status(thm)],[c_22,c_413])).

tff(c_5714,plain,(
    ! [A_540,C_541,D_542] :
      ( k13_lattice3(A_540,C_541,'#skF_3'(A_540,k2_tarski(C_541,D_542))) = '#skF_3'(A_540,k2_tarski(C_541,D_542))
      | ~ v1_lattice3(A_540)
      | ~ r2_lattice3(A_540,k2_tarski(C_541,D_542),'#skF_3'(A_540,k2_tarski(C_541,D_542)))
      | ~ m1_subset_1('#skF_3'(A_540,k2_tarski(C_541,D_542)),u1_struct_0(A_540))
      | ~ m1_subset_1(D_542,u1_struct_0(A_540))
      | ~ m1_subset_1(C_541,u1_struct_0(A_540))
      | ~ r1_yellow_0(A_540,k2_tarski(C_541,D_542))
      | ~ l1_orders_2(A_540)
      | ~ v5_orders_2(A_540) ) ),
    inference(resolution,[status(thm)],[c_385,c_527])).

tff(c_5788,plain,(
    ! [A_22,C_541,D_542] :
      ( k13_lattice3(A_22,C_541,'#skF_3'(A_22,k2_tarski(C_541,D_542))) = '#skF_3'(A_22,k2_tarski(C_541,D_542))
      | ~ v1_lattice3(A_22)
      | ~ m1_subset_1('#skF_3'(A_22,k2_tarski(C_541,D_542)),u1_struct_0(A_22))
      | ~ m1_subset_1(D_542,u1_struct_0(A_22))
      | ~ m1_subset_1(C_541,u1_struct_0(A_22))
      | ~ r1_yellow_0(A_22,k2_tarski(C_541,D_542))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22) ) ),
    inference(resolution,[status(thm)],[c_24,c_5714])).

tff(c_70897,plain,
    ( k13_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))) = '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ v1_lattice3('#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_70894,c_5788])).

tff(c_70928,plain,(
    k13_lattice3('#skF_5','#skF_7','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))) = '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_70624,c_62,c_64,c_68,c_70897])).

tff(c_71323,plain,
    ( r1_orders_2('#skF_5','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),'#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v1_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_70928,c_346])).

tff(c_71425,plain,(
    r1_orders_2('#skF_5','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),'#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_62,c_70894,c_71323])).

tff(c_71434,plain,
    ( k13_lattice3('#skF_5','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),k13_lattice3('#skF_5','#skF_6','#skF_7')) = '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_71425,c_55643])).

tff(c_71475,plain,(
    k13_lattice3('#skF_5','#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),k13_lattice3('#skF_5','#skF_6','#skF_7')) = '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70894,c_71003,c_71000,c_71434])).

tff(c_72400,plain,
    ( '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')) = k13_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_7','#skF_6'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_71475,c_45512])).

tff(c_72525,plain,(
    '#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')) = k13_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70624,c_55728,c_72400])).

tff(c_72673,plain,
    ( ~ r1_yellow_0('#skF_5',k2_tarski('#skF_7','#skF_6'))
    | ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),'#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')))
    | ~ m1_subset_1('#skF_3'('#skF_5',k2_tarski('#skF_7','#skF_6')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_72525,c_12395])).

tff(c_73034,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_32158,c_72525,c_72525,c_64,c_62,c_70624,c_72673])).

tff(c_73035,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_70895,c_73034])).

tff(c_74198,plain,(
    ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_73035])).

tff(c_74201,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_orders_2('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_74198])).

tff(c_74205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32158,c_64,c_62,c_32157,c_33224,c_74201])).

tff(c_74207,plain,(
    r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_73035])).

tff(c_74206,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_73035])).

tff(c_74333,plain,
    ( r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_74206])).

tff(c_74336,plain,(
    r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_32158,c_74207,c_74333])).

tff(c_74338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70895,c_74336])).

tff(c_74340,plain,(
    r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_55011])).

tff(c_74347,plain,
    ( k1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) = '#skF_3'('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_74340,c_689])).

tff(c_74356,plain,(
    k1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) = '#skF_3'('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_74347])).

tff(c_74437,plain,(
    '#skF_3'('#skF_5',k2_tarski('#skF_6','#skF_7')) != k13_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74356,c_137])).

tff(c_74339,plain,
    ( ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_1'('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_55011])).

tff(c_77227,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_74339])).

tff(c_77230,plain,
    ( k1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7')) = k13_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_yellow_0('#skF_5',k2_tarski('#skF_6','#skF_7'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_77227])).

tff(c_77233,plain,
    ( '#skF_3'('#skF_5',k2_tarski('#skF_6','#skF_7')) = k13_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32158,c_74340,c_74356,c_77230])).

tff(c_77234,plain,(
    ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_74437,c_77233])).

tff(c_77237,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_orders_2('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_77234])).

tff(c_77241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32158,c_64,c_62,c_32157,c_33224,c_77237])).

tff(c_77242,plain,(
    ~ r2_lattice3('#skF_5',k2_tarski('#skF_6','#skF_7'),k13_lattice3('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_74339])).

tff(c_77246,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ r1_orders_2('#skF_5','#skF_6',k13_lattice3('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k13_lattice3('#skF_5','#skF_6','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_77242])).

tff(c_77250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32158,c_64,c_62,c_32157,c_33224,c_77246])).

%------------------------------------------------------------------------------
