%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:35 EST 2020

% Result     : Theorem 10.49s
% Output     : CNFRefutation 10.49s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 107 expanded)
%              Number of leaves         :   35 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  147 ( 309 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_orders_2)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ~ ( ? [D] :
                        ( v6_orders_2(D,A)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(B,D)
                        & r2_hidden(C,D) )
                    & ~ r1_orders_2(A,B,C)
                    & ~ r1_orders_2(A,C,B) )
                & ~ ( ( r1_orders_2(A,B,C)
                      | r1_orders_2(A,C,B) )
                    & ! [D] :
                        ( ( v6_orders_2(D,A)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                       => ~ ( r2_hidden(B,D)
                            & r2_hidden(C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_143,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( r2_hidden(B,C)
                  & r2_hidden(B,k1_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).

tff(c_66,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_60,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_168,plain,(
    ! [A_85,B_86] :
      ( k6_domain_1(A_85,B_86) = k1_tarski(B_86)
      | ~ m1_subset_1(B_86,A_85)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_176,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_168])).

tff(c_181,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_192,plain,(
    ! [A_93,B_94] :
      ( r1_orders_2(A_93,B_94,B_94)
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93)
      | ~ v3_orders_2(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_194,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_5')
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_192])).

tff(c_197,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_194])).

tff(c_198,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_197])).

tff(c_38,plain,(
    ! [A_25,C_43,B_37] :
      ( ~ r1_orders_2(A_25,C_43,B_37)
      | r2_hidden(C_43,'#skF_3'(A_25,B_37,C_43))
      | ~ m1_subset_1(C_43,u1_struct_0(A_25))
      | ~ m1_subset_1(B_37,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25)
      | ~ v3_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_7115,plain,(
    ! [A_7680,C_7681,B_7682] :
      ( ~ r1_orders_2(A_7680,C_7681,B_7682)
      | m1_subset_1('#skF_3'(A_7680,B_7682,C_7681),k1_zfmisc_1(u1_struct_0(A_7680)))
      | ~ m1_subset_1(C_7681,u1_struct_0(A_7680))
      | ~ m1_subset_1(B_7682,u1_struct_0(A_7680))
      | ~ l1_orders_2(A_7680)
      | ~ v3_orders_2(A_7680) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    ! [C_19,B_18,A_17] :
      ( ~ v1_xboole_0(C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(C_19))
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_13800,plain,(
    ! [A_9839,A_9840,B_9841,C_9842] :
      ( ~ v1_xboole_0(u1_struct_0(A_9839))
      | ~ r2_hidden(A_9840,'#skF_3'(A_9839,B_9841,C_9842))
      | ~ r1_orders_2(A_9839,C_9842,B_9841)
      | ~ m1_subset_1(C_9842,u1_struct_0(A_9839))
      | ~ m1_subset_1(B_9841,u1_struct_0(A_9839))
      | ~ l1_orders_2(A_9839)
      | ~ v3_orders_2(A_9839) ) ),
    inference(resolution,[status(thm)],[c_7115,c_30])).

tff(c_15882,plain,(
    ! [A_10751,C_10752,B_10753] :
      ( ~ v1_xboole_0(u1_struct_0(A_10751))
      | ~ r1_orders_2(A_10751,C_10752,B_10753)
      | ~ m1_subset_1(C_10752,u1_struct_0(A_10751))
      | ~ m1_subset_1(B_10753,u1_struct_0(A_10751))
      | ~ l1_orders_2(A_10751)
      | ~ v3_orders_2(A_10751) ) ),
    inference(resolution,[status(thm)],[c_38,c_13800])).

tff(c_15884,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_198,c_15882])).

tff(c_15888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_58,c_181,c_15884])).

tff(c_15890,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k1_tarski(A_10),k1_zfmisc_1(B_11))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_64,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_62,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_78,plain,(
    ! [D_56,A_57] : r2_hidden(D_56,k2_tarski(A_57,D_56)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_81,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_78])).

tff(c_15889,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_56,plain,(
    r2_hidden('#skF_5',k1_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_15899,plain,(
    r2_hidden('#skF_5',k1_orders_2('#skF_4',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15889,c_56])).

tff(c_23524,plain,(
    ! [B_18687,A_18688,C_18689] :
      ( ~ r2_hidden(B_18687,k1_orders_2(A_18688,C_18689))
      | ~ r2_hidden(B_18687,C_18689)
      | ~ m1_subset_1(C_18689,k1_zfmisc_1(u1_struct_0(A_18688)))
      | ~ m1_subset_1(B_18687,u1_struct_0(A_18688))
      | ~ l1_orders_2(A_18688)
      | ~ v5_orders_2(A_18688)
      | ~ v4_orders_2(A_18688)
      | ~ v3_orders_2(A_18688)
      | v2_struct_0(A_18688) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_23535,plain,
    ( ~ r2_hidden('#skF_5',k1_tarski('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_15899,c_23524])).

tff(c_23543,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_81,c_23535])).

tff(c_23544,plain,(
    ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_23543])).

tff(c_23557,plain,(
    ~ r2_hidden('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_23544])).

tff(c_23561,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_23557])).

tff(c_23564,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_23561])).

tff(c_23566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15890,c_23564])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:04:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.49/3.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.49/3.91  
% 10.49/3.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.49/3.91  %$ r1_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 10.49/3.91  
% 10.49/3.91  %Foreground sorts:
% 10.49/3.91  
% 10.49/3.91  
% 10.49/3.91  %Background operators:
% 10.49/3.91  
% 10.49/3.91  
% 10.49/3.91  %Foreground operators:
% 10.49/3.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.49/3.91  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.49/3.91  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 10.49/3.91  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 10.49/3.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.49/3.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.49/3.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.49/3.91  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 10.49/3.91  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 10.49/3.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.49/3.91  tff('#skF_5', type, '#skF_5': $i).
% 10.49/3.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.49/3.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.49/3.91  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 10.49/3.91  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 10.49/3.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.49/3.91  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 10.49/3.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.49/3.91  tff('#skF_4', type, '#skF_4': $i).
% 10.49/3.91  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.49/3.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.49/3.91  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 10.49/3.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.49/3.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.49/3.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.49/3.91  
% 10.49/3.92  tff(f_161, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_orders_2)).
% 10.49/3.92  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 10.49/3.92  tff(f_80, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 10.49/3.92  tff(f_121, axiom, (![A]: ((v3_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~(((?[D]: (((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) & r2_hidden(B, D)) & r2_hidden(C, D))) & ~r1_orders_2(A, B, C)) & ~r1_orders_2(A, C, B)) & ~((r1_orders_2(A, B, C) | r1_orders_2(A, C, B)) & (![D]: ((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~(r2_hidden(B, D) & r2_hidden(C, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_orders_2)).
% 10.49/3.92  tff(f_61, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 10.49/3.92  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 10.49/3.92  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 10.49/3.92  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 10.49/3.92  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 10.49/3.92  tff(f_143, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_orders_2)).
% 10.49/3.92  tff(c_66, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.49/3.92  tff(c_60, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.49/3.92  tff(c_58, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.49/3.92  tff(c_168, plain, (![A_85, B_86]: (k6_domain_1(A_85, B_86)=k1_tarski(B_86) | ~m1_subset_1(B_86, A_85) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.49/3.92  tff(c_176, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_168])).
% 10.49/3.92  tff(c_181, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_176])).
% 10.49/3.92  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.49/3.92  tff(c_192, plain, (![A_93, B_94]: (r1_orders_2(A_93, B_94, B_94) | ~m1_subset_1(B_94, u1_struct_0(A_93)) | ~l1_orders_2(A_93) | ~v3_orders_2(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.49/3.92  tff(c_194, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5') | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_192])).
% 10.49/3.92  tff(c_197, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_60, c_194])).
% 10.49/3.92  tff(c_198, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_197])).
% 10.49/3.92  tff(c_38, plain, (![A_25, C_43, B_37]: (~r1_orders_2(A_25, C_43, B_37) | r2_hidden(C_43, '#skF_3'(A_25, B_37, C_43)) | ~m1_subset_1(C_43, u1_struct_0(A_25)) | ~m1_subset_1(B_37, u1_struct_0(A_25)) | ~l1_orders_2(A_25) | ~v3_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.49/3.92  tff(c_7115, plain, (![A_7680, C_7681, B_7682]: (~r1_orders_2(A_7680, C_7681, B_7682) | m1_subset_1('#skF_3'(A_7680, B_7682, C_7681), k1_zfmisc_1(u1_struct_0(A_7680))) | ~m1_subset_1(C_7681, u1_struct_0(A_7680)) | ~m1_subset_1(B_7682, u1_struct_0(A_7680)) | ~l1_orders_2(A_7680) | ~v3_orders_2(A_7680))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.49/3.92  tff(c_30, plain, (![C_19, B_18, A_17]: (~v1_xboole_0(C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(C_19)) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.49/3.92  tff(c_13800, plain, (![A_9839, A_9840, B_9841, C_9842]: (~v1_xboole_0(u1_struct_0(A_9839)) | ~r2_hidden(A_9840, '#skF_3'(A_9839, B_9841, C_9842)) | ~r1_orders_2(A_9839, C_9842, B_9841) | ~m1_subset_1(C_9842, u1_struct_0(A_9839)) | ~m1_subset_1(B_9841, u1_struct_0(A_9839)) | ~l1_orders_2(A_9839) | ~v3_orders_2(A_9839))), inference(resolution, [status(thm)], [c_7115, c_30])).
% 10.49/3.92  tff(c_15882, plain, (![A_10751, C_10752, B_10753]: (~v1_xboole_0(u1_struct_0(A_10751)) | ~r1_orders_2(A_10751, C_10752, B_10753) | ~m1_subset_1(C_10752, u1_struct_0(A_10751)) | ~m1_subset_1(B_10753, u1_struct_0(A_10751)) | ~l1_orders_2(A_10751) | ~v3_orders_2(A_10751))), inference(resolution, [status(thm)], [c_38, c_13800])).
% 10.49/3.92  tff(c_15884, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_198, c_15882])).
% 10.49/3.92  tff(c_15888, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_60, c_58, c_181, c_15884])).
% 10.49/3.92  tff(c_15890, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_176])).
% 10.49/3.92  tff(c_26, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.49/3.92  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(k1_tarski(A_10), k1_zfmisc_1(B_11)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.49/3.92  tff(c_64, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.49/3.92  tff(c_62, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.49/3.92  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.49/3.92  tff(c_78, plain, (![D_56, A_57]: (r2_hidden(D_56, k2_tarski(A_57, D_56)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.49/3.92  tff(c_81, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_78])).
% 10.49/3.92  tff(c_15889, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_176])).
% 10.49/3.92  tff(c_56, plain, (r2_hidden('#skF_5', k1_orders_2('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.49/3.92  tff(c_15899, plain, (r2_hidden('#skF_5', k1_orders_2('#skF_4', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_15889, c_56])).
% 10.49/3.92  tff(c_23524, plain, (![B_18687, A_18688, C_18689]: (~r2_hidden(B_18687, k1_orders_2(A_18688, C_18689)) | ~r2_hidden(B_18687, C_18689) | ~m1_subset_1(C_18689, k1_zfmisc_1(u1_struct_0(A_18688))) | ~m1_subset_1(B_18687, u1_struct_0(A_18688)) | ~l1_orders_2(A_18688) | ~v5_orders_2(A_18688) | ~v4_orders_2(A_18688) | ~v3_orders_2(A_18688) | v2_struct_0(A_18688))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.49/3.92  tff(c_23535, plain, (~r2_hidden('#skF_5', k1_tarski('#skF_5')) | ~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_15899, c_23524])).
% 10.49/3.92  tff(c_23543, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_81, c_23535])).
% 10.49/3.92  tff(c_23544, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_23543])).
% 10.49/3.92  tff(c_23557, plain, (~r2_hidden('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_23544])).
% 10.49/3.92  tff(c_23561, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_23557])).
% 10.49/3.92  tff(c_23564, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_23561])).
% 10.49/3.92  tff(c_23566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15890, c_23564])).
% 10.49/3.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.49/3.92  
% 10.49/3.92  Inference rules
% 10.49/3.92  ----------------------
% 10.49/3.92  #Ref     : 0
% 10.49/3.92  #Sup     : 4210
% 10.49/3.92  #Fact    : 78
% 10.49/3.92  #Define  : 0
% 10.49/3.92  #Split   : 14
% 10.49/3.92  #Chain   : 0
% 10.49/3.92  #Close   : 0
% 10.49/3.92  
% 10.49/3.92  Ordering : KBO
% 10.49/3.92  
% 10.49/3.92  Simplification rules
% 10.49/3.92  ----------------------
% 10.49/3.92  #Subsume      : 1541
% 10.49/3.92  #Demod        : 661
% 10.49/3.92  #Tautology    : 1339
% 10.49/3.92  #SimpNegUnit  : 128
% 10.49/3.92  #BackRed      : 2
% 10.49/3.92  
% 10.49/3.92  #Partial instantiations: 10440
% 10.49/3.92  #Strategies tried      : 1
% 10.49/3.92  
% 10.49/3.92  Timing (in seconds)
% 10.49/3.92  ----------------------
% 10.49/3.93  Preprocessing        : 0.35
% 10.49/3.93  Parsing              : 0.18
% 10.49/3.93  CNF conversion       : 0.03
% 10.49/3.93  Main loop            : 2.80
% 10.49/3.93  Inferencing          : 1.11
% 10.49/3.93  Reduction            : 0.66
% 10.49/3.93  Demodulation         : 0.45
% 10.49/3.93  BG Simplification    : 0.11
% 10.49/3.93  Subsumption          : 0.77
% 10.49/3.93  Abstraction          : 0.17
% 10.49/3.93  MUC search           : 0.00
% 10.49/3.93  Cooper               : 0.00
% 10.49/3.93  Total                : 3.18
% 10.49/3.93  Index Insertion      : 0.00
% 10.49/3.93  Index Deletion       : 0.00
% 10.49/3.93  Index Matching       : 0.00
% 10.49/3.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
