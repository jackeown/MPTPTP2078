%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:08 EST 2020

% Result     : Theorem 5.14s
% Output     : CNFRefutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 349 expanded)
%              Number of leaves         :   52 ( 144 expanded)
%              Depth                    :   12
%              Number of atoms          :  241 ( 864 expanded)
%              Number of equality atoms :   29 ( 137 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_xboole_0 > k4_orders_2 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_222,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_59,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_101,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_100,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_73,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
        & r1_xboole_0(C,A)
        & r1_xboole_0(D,B) )
     => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r2_hidden(C,A)
        | r1_tarski(A,k4_xboole_0(B,k1_tarski(C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_zfmisc_1)).

tff(f_181,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( C = k4_orders_2(A,B)
            <=> ! [D] :
                  ( r2_hidden(D,C)
                <=> m2_orders_2(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_204,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => ! [D] :
                  ( m2_orders_2(D,A,B)
                 => ~ r1_xboole_0(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).

tff(f_91,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

tff(c_160,plain,(
    ! [A_111,B_112] : k4_xboole_0(A_111,k4_xboole_0(A_111,B_112)) = k3_xboole_0(A_111,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_196,plain,(
    ! [B_113] : k3_xboole_0(k1_xboole_0,B_113) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_18])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_201,plain,(
    ! [B_113,C_10] :
      ( ~ r1_xboole_0(k1_xboole_0,B_113)
      | ~ r2_hidden(C_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_10])).

tff(c_234,plain,(
    ! [C_10] : ~ r2_hidden(C_10,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_78,plain,(
    v3_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_76,plain,(
    v4_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_74,plain,(
    v5_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_72,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_70,plain,(
    m1_orders_1('#skF_8',k1_orders_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_12,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_68,plain,(
    k3_tarski(k4_orders_2('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_111,plain,(
    ! [A_95] : r1_tarski(A_95,k1_zfmisc_1(k3_tarski(A_95))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_114,plain,(
    r1_tarski(k4_orders_2('#skF_7','#skF_8'),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_111])).

tff(c_115,plain,(
    r1_tarski(k4_orders_2('#skF_7','#skF_8'),k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_114])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(k1_tarski(A_30),B_31)
      | r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_297,plain,(
    ! [A_128,C_129,B_130] :
      ( r1_xboole_0(A_128,C_129)
      | ~ r1_xboole_0(B_130,C_129)
      | ~ r1_tarski(A_128,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_439,plain,(
    ! [A_155,B_156,A_157] :
      ( r1_xboole_0(A_155,B_156)
      | ~ r1_tarski(A_155,k1_tarski(A_157))
      | r2_hidden(A_157,B_156) ) ),
    inference(resolution,[status(thm)],[c_32,c_297])).

tff(c_445,plain,(
    ! [B_156] :
      ( r1_xboole_0(k4_orders_2('#skF_7','#skF_8'),B_156)
      | r2_hidden(k1_xboole_0,B_156) ) ),
    inference(resolution,[status(thm)],[c_115,c_439])).

tff(c_22,plain,(
    ! [A_20] : r1_xboole_0(A_20,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_561,plain,(
    ! [C_174,B_175,D_176,A_177] :
      ( C_174 = B_175
      | ~ r1_xboole_0(D_176,B_175)
      | ~ r1_xboole_0(C_174,A_177)
      | k2_xboole_0(C_174,D_176) != k2_xboole_0(A_177,B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_680,plain,(
    ! [C_196,A_197,A_198] :
      ( k1_xboole_0 = C_196
      | ~ r1_xboole_0(C_196,A_197)
      | k2_xboole_0(C_196,A_198) != k2_xboole_0(A_197,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_561])).

tff(c_704,plain,(
    ! [A_198,B_156] :
      ( k4_orders_2('#skF_7','#skF_8') = k1_xboole_0
      | k2_xboole_0(k4_orders_2('#skF_7','#skF_8'),A_198) != k2_xboole_0(B_156,k1_xboole_0)
      | r2_hidden(k1_xboole_0,B_156) ) ),
    inference(resolution,[status(thm)],[c_445,c_680])).

tff(c_999,plain,(
    k4_orders_2('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_704])).

tff(c_38,plain,(
    ! [A_33,B_34,C_35] :
      ( r1_tarski(A_33,k4_xboole_0(B_34,k1_tarski(C_35)))
      | r2_hidden(C_35,A_33)
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_723,plain,(
    ! [A_201,B_202] :
      ( ~ v1_xboole_0(k4_orders_2(A_201,B_202))
      | ~ m1_orders_1(B_202,k1_orders_1(u1_struct_0(A_201)))
      | ~ l1_orders_2(A_201)
      | ~ v5_orders_2(A_201)
      | ~ v4_orders_2(A_201)
      | ~ v3_orders_2(A_201)
      | v2_struct_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_726,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_7','#skF_8'))
    | ~ l1_orders_2('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_723])).

tff(c_729,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_7','#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_726])).

tff(c_730,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_729])).

tff(c_456,plain,(
    ! [B_161] :
      ( r1_xboole_0(k4_orders_2('#skF_7','#skF_8'),B_161)
      | r2_hidden(k1_xboole_0,B_161) ) ),
    inference(resolution,[status(thm)],[c_115,c_439])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( ~ r1_xboole_0(B_22,A_21)
      | ~ r1_tarski(B_22,A_21)
      | v1_xboole_0(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_466,plain,(
    ! [B_161] :
      ( ~ r1_tarski(k4_orders_2('#skF_7','#skF_8'),B_161)
      | v1_xboole_0(k4_orders_2('#skF_7','#skF_8'))
      | r2_hidden(k1_xboole_0,B_161) ) ),
    inference(resolution,[status(thm)],[c_456,c_24])).

tff(c_770,plain,(
    ! [B_209] :
      ( ~ r1_tarski(k4_orders_2('#skF_7','#skF_8'),B_209)
      | r2_hidden(k1_xboole_0,B_209) ) ),
    inference(negUnitSimplification,[status(thm)],[c_730,c_466])).

tff(c_866,plain,(
    ! [B_217,C_218] :
      ( r2_hidden(k1_xboole_0,k4_xboole_0(B_217,k1_tarski(C_218)))
      | r2_hidden(C_218,k4_orders_2('#skF_7','#skF_8'))
      | ~ r1_tarski(k4_orders_2('#skF_7','#skF_8'),B_217) ) ),
    inference(resolution,[status(thm)],[c_38,c_770])).

tff(c_885,plain,(
    ! [C_218] :
      ( r2_hidden(k1_xboole_0,k1_xboole_0)
      | r2_hidden(C_218,k4_orders_2('#skF_7','#skF_8'))
      | ~ r1_tarski(k4_orders_2('#skF_7','#skF_8'),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_866])).

tff(c_893,plain,(
    ! [C_218] :
      ( r2_hidden(C_218,k4_orders_2('#skF_7','#skF_8'))
      | ~ r1_tarski(k4_orders_2('#skF_7','#skF_8'),k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_885])).

tff(c_894,plain,(
    ~ r1_tarski(k4_orders_2('#skF_7','#skF_8'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_893])).

tff(c_1000,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_999,c_894])).

tff(c_1011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1000])).

tff(c_1012,plain,(
    ! [A_198,B_156] :
      ( k2_xboole_0(k4_orders_2('#skF_7','#skF_8'),A_198) != k2_xboole_0(B_156,k1_xboole_0)
      | r2_hidden(k1_xboole_0,B_156) ) ),
    inference(splitRight,[status(thm)],[c_704])).

tff(c_1196,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_7','#skF_8')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1012])).

tff(c_50,plain,(
    ! [D_67,A_46,B_58] :
      ( m2_orders_2(D_67,A_46,B_58)
      | ~ r2_hidden(D_67,k4_orders_2(A_46,B_58))
      | ~ m1_orders_1(B_58,k1_orders_1(u1_struct_0(A_46)))
      | ~ l1_orders_2(A_46)
      | ~ v5_orders_2(A_46)
      | ~ v4_orders_2(A_46)
      | ~ v3_orders_2(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1216,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_7','#skF_8')
    | ~ m1_orders_1('#skF_8',k1_orders_1(u1_struct_0('#skF_7')))
    | ~ l1_orders_2('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1196,c_50])).

tff(c_1233,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_7','#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_1216])).

tff(c_1234,plain,(
    m2_orders_2(k1_xboole_0,'#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1233])).

tff(c_1013,plain,(
    k4_orders_2('#skF_7','#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_704])).

tff(c_179,plain,(
    ! [B_112] : k3_xboole_0(k1_xboole_0,B_112) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_18])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_235,plain,(
    ! [C_117] : ~ r2_hidden(C_117,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_246,plain,(
    ! [B_2] : r1_xboole_0(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_235])).

tff(c_1651,plain,(
    ! [A_305,B_306,C_307] :
      ( m2_orders_2('#skF_4'(A_305,B_306,C_307),A_305,B_306)
      | r2_hidden('#skF_5'(A_305,B_306,C_307),C_307)
      | k4_orders_2(A_305,B_306) = C_307
      | ~ m1_orders_1(B_306,k1_orders_1(u1_struct_0(A_305)))
      | ~ l1_orders_2(A_305)
      | ~ v5_orders_2(A_305)
      | ~ v4_orders_2(A_305)
      | ~ v3_orders_2(A_305)
      | v2_struct_0(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1653,plain,(
    ! [C_307] :
      ( m2_orders_2('#skF_4'('#skF_7','#skF_8',C_307),'#skF_7','#skF_8')
      | r2_hidden('#skF_5'('#skF_7','#skF_8',C_307),C_307)
      | k4_orders_2('#skF_7','#skF_8') = C_307
      | ~ l1_orders_2('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | ~ v3_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_1651])).

tff(c_1656,plain,(
    ! [C_307] :
      ( m2_orders_2('#skF_4'('#skF_7','#skF_8',C_307),'#skF_7','#skF_8')
      | r2_hidden('#skF_5'('#skF_7','#skF_8',C_307),C_307)
      | k4_orders_2('#skF_7','#skF_8') = C_307
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_1653])).

tff(c_1698,plain,(
    ! [C_313] :
      ( m2_orders_2('#skF_4'('#skF_7','#skF_8',C_313),'#skF_7','#skF_8')
      | r2_hidden('#skF_5'('#skF_7','#skF_8',C_313),C_313)
      | k4_orders_2('#skF_7','#skF_8') = C_313 ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1656])).

tff(c_1975,plain,(
    ! [A_333,B_334] :
      ( ~ r1_xboole_0(A_333,B_334)
      | m2_orders_2('#skF_4'('#skF_7','#skF_8',k3_xboole_0(A_333,B_334)),'#skF_7','#skF_8')
      | k4_orders_2('#skF_7','#skF_8') = k3_xboole_0(A_333,B_334) ) ),
    inference(resolution,[status(thm)],[c_1698,c_10])).

tff(c_1978,plain,(
    ! [B_112] :
      ( ~ r1_xboole_0(k1_xboole_0,B_112)
      | m2_orders_2('#skF_4'('#skF_7','#skF_8',k1_xboole_0),'#skF_7','#skF_8')
      | k4_orders_2('#skF_7','#skF_8') = k3_xboole_0(k1_xboole_0,B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_1975])).

tff(c_1980,plain,
    ( m2_orders_2('#skF_4'('#skF_7','#skF_8',k1_xboole_0),'#skF_7','#skF_8')
    | k4_orders_2('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_246,c_1978])).

tff(c_1981,plain,(
    m2_orders_2('#skF_4'('#skF_7','#skF_8',k1_xboole_0),'#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1013,c_1980])).

tff(c_1253,plain,(
    ! [C_249,D_250,A_251,B_252] :
      ( ~ r1_xboole_0(C_249,D_250)
      | ~ m2_orders_2(D_250,A_251,B_252)
      | ~ m2_orders_2(C_249,A_251,B_252)
      | ~ m1_orders_1(B_252,k1_orders_1(u1_struct_0(A_251)))
      | ~ l1_orders_2(A_251)
      | ~ v5_orders_2(A_251)
      | ~ v4_orders_2(A_251)
      | ~ v3_orders_2(A_251)
      | v2_struct_0(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_2941,plain,(
    ! [A_424,B_425,A_426] :
      ( ~ m2_orders_2(k1_xboole_0,A_424,B_425)
      | ~ m2_orders_2(A_426,A_424,B_425)
      | ~ m1_orders_1(B_425,k1_orders_1(u1_struct_0(A_424)))
      | ~ l1_orders_2(A_424)
      | ~ v5_orders_2(A_424)
      | ~ v4_orders_2(A_424)
      | ~ v3_orders_2(A_424)
      | v2_struct_0(A_424) ) ),
    inference(resolution,[status(thm)],[c_22,c_1253])).

tff(c_2947,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_7','#skF_8')
    | ~ m1_orders_1('#skF_8',k1_orders_1(u1_struct_0('#skF_7')))
    | ~ l1_orders_2('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1981,c_2941])).

tff(c_2968,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_1234,c_2947])).

tff(c_2970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2968])).

tff(c_2972,plain,(
    r1_tarski(k4_orders_2('#skF_7','#skF_8'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_893])).

tff(c_769,plain,(
    ! [B_161] :
      ( ~ r1_tarski(k4_orders_2('#skF_7','#skF_8'),B_161)
      | r2_hidden(k1_xboole_0,B_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_730,c_466])).

tff(c_2997,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2972,c_769])).

tff(c_3006,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_2997])).

tff(c_3007,plain,(
    ! [B_113] : ~ r1_xboole_0(k1_xboole_0,B_113) ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_120,plain,(
    ! [A_97,B_98] : r1_xboole_0(k4_xboole_0(A_97,B_98),k4_xboole_0(B_98,A_97)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_123,plain,(
    ! [A_16] : r1_xboole_0(k1_xboole_0,k4_xboole_0(A_16,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_120])).

tff(c_3009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3007,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:29:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.14/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/2.06  
% 5.14/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/2.06  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_xboole_0 > k4_orders_2 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 5.14/2.06  
% 5.14/2.06  %Foreground sorts:
% 5.14/2.06  
% 5.14/2.06  
% 5.14/2.06  %Background operators:
% 5.14/2.06  
% 5.14/2.06  
% 5.14/2.06  %Foreground operators:
% 5.14/2.06  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 5.14/2.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.14/2.06  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.14/2.06  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.14/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.14/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.14/2.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.14/2.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.14/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.14/2.06  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 5.14/2.06  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.14/2.06  tff('#skF_7', type, '#skF_7': $i).
% 5.14/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.14/2.06  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 5.14/2.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.14/2.06  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.14/2.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.14/2.06  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.14/2.06  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.14/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.14/2.06  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.14/2.06  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 5.14/2.06  tff('#skF_8', type, '#skF_8': $i).
% 5.14/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.14/2.06  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.14/2.06  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.14/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.14/2.06  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.14/2.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.14/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.14/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.14/2.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.14/2.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.14/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.14/2.06  
% 5.44/2.08  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.44/2.08  tff(f_65, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 5.44/2.08  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.44/2.08  tff(f_222, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 5.44/2.08  tff(f_59, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.44/2.08  tff(f_101, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 5.44/2.09  tff(f_100, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 5.44/2.09  tff(f_98, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 5.44/2.09  tff(f_71, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 5.44/2.09  tff(f_73, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.44/2.09  tff(f_89, axiom, (![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 5.44/2.09  tff(f_107, axiom, (![A, B, C]: (r1_tarski(A, B) => (r2_hidden(C, A) | r1_tarski(A, k4_xboole_0(B, k1_tarski(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_zfmisc_1)).
% 5.44/2.09  tff(f_181, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 5.44/2.09  tff(f_81, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 5.44/2.09  tff(f_149, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 5.44/2.09  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.44/2.09  tff(f_204, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 5.44/2.09  tff(f_91, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 5.44/2.09  tff(c_160, plain, (![A_111, B_112]: (k4_xboole_0(A_111, k4_xboole_0(A_111, B_112))=k3_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.44/2.09  tff(c_18, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.44/2.09  tff(c_196, plain, (![B_113]: (k3_xboole_0(k1_xboole_0, B_113)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_160, c_18])).
% 5.44/2.09  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.44/2.09  tff(c_201, plain, (![B_113, C_10]: (~r1_xboole_0(k1_xboole_0, B_113) | ~r2_hidden(C_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_196, c_10])).
% 5.44/2.09  tff(c_234, plain, (![C_10]: (~r2_hidden(C_10, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_201])).
% 5.44/2.09  tff(c_80, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.44/2.09  tff(c_78, plain, (v3_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.44/2.09  tff(c_76, plain, (v4_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.44/2.09  tff(c_74, plain, (v5_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.44/2.09  tff(c_72, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.44/2.09  tff(c_70, plain, (m1_orders_1('#skF_8', k1_orders_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.44/2.09  tff(c_12, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.44/2.09  tff(c_36, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.44/2.09  tff(c_68, plain, (k3_tarski(k4_orders_2('#skF_7', '#skF_8'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.44/2.09  tff(c_111, plain, (![A_95]: (r1_tarski(A_95, k1_zfmisc_1(k3_tarski(A_95))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.44/2.09  tff(c_114, plain, (r1_tarski(k4_orders_2('#skF_7', '#skF_8'), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_68, c_111])).
% 5.44/2.09  tff(c_115, plain, (r1_tarski(k4_orders_2('#skF_7', '#skF_8'), k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_114])).
% 5.44/2.09  tff(c_32, plain, (![A_30, B_31]: (r1_xboole_0(k1_tarski(A_30), B_31) | r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.44/2.09  tff(c_297, plain, (![A_128, C_129, B_130]: (r1_xboole_0(A_128, C_129) | ~r1_xboole_0(B_130, C_129) | ~r1_tarski(A_128, B_130))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.44/2.09  tff(c_439, plain, (![A_155, B_156, A_157]: (r1_xboole_0(A_155, B_156) | ~r1_tarski(A_155, k1_tarski(A_157)) | r2_hidden(A_157, B_156))), inference(resolution, [status(thm)], [c_32, c_297])).
% 5.44/2.09  tff(c_445, plain, (![B_156]: (r1_xboole_0(k4_orders_2('#skF_7', '#skF_8'), B_156) | r2_hidden(k1_xboole_0, B_156))), inference(resolution, [status(thm)], [c_115, c_439])).
% 5.44/2.09  tff(c_22, plain, (![A_20]: (r1_xboole_0(A_20, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.44/2.09  tff(c_561, plain, (![C_174, B_175, D_176, A_177]: (C_174=B_175 | ~r1_xboole_0(D_176, B_175) | ~r1_xboole_0(C_174, A_177) | k2_xboole_0(C_174, D_176)!=k2_xboole_0(A_177, B_175))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.44/2.09  tff(c_680, plain, (![C_196, A_197, A_198]: (k1_xboole_0=C_196 | ~r1_xboole_0(C_196, A_197) | k2_xboole_0(C_196, A_198)!=k2_xboole_0(A_197, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_561])).
% 5.44/2.09  tff(c_704, plain, (![A_198, B_156]: (k4_orders_2('#skF_7', '#skF_8')=k1_xboole_0 | k2_xboole_0(k4_orders_2('#skF_7', '#skF_8'), A_198)!=k2_xboole_0(B_156, k1_xboole_0) | r2_hidden(k1_xboole_0, B_156))), inference(resolution, [status(thm)], [c_445, c_680])).
% 5.44/2.09  tff(c_999, plain, (k4_orders_2('#skF_7', '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_704])).
% 5.44/2.09  tff(c_38, plain, (![A_33, B_34, C_35]: (r1_tarski(A_33, k4_xboole_0(B_34, k1_tarski(C_35))) | r2_hidden(C_35, A_33) | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.44/2.09  tff(c_723, plain, (![A_201, B_202]: (~v1_xboole_0(k4_orders_2(A_201, B_202)) | ~m1_orders_1(B_202, k1_orders_1(u1_struct_0(A_201))) | ~l1_orders_2(A_201) | ~v5_orders_2(A_201) | ~v4_orders_2(A_201) | ~v3_orders_2(A_201) | v2_struct_0(A_201))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.44/2.09  tff(c_726, plain, (~v1_xboole_0(k4_orders_2('#skF_7', '#skF_8')) | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_70, c_723])).
% 5.44/2.09  tff(c_729, plain, (~v1_xboole_0(k4_orders_2('#skF_7', '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_726])).
% 5.44/2.09  tff(c_730, plain, (~v1_xboole_0(k4_orders_2('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_80, c_729])).
% 5.44/2.09  tff(c_456, plain, (![B_161]: (r1_xboole_0(k4_orders_2('#skF_7', '#skF_8'), B_161) | r2_hidden(k1_xboole_0, B_161))), inference(resolution, [status(thm)], [c_115, c_439])).
% 5.44/2.09  tff(c_24, plain, (![B_22, A_21]: (~r1_xboole_0(B_22, A_21) | ~r1_tarski(B_22, A_21) | v1_xboole_0(B_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.44/2.09  tff(c_466, plain, (![B_161]: (~r1_tarski(k4_orders_2('#skF_7', '#skF_8'), B_161) | v1_xboole_0(k4_orders_2('#skF_7', '#skF_8')) | r2_hidden(k1_xboole_0, B_161))), inference(resolution, [status(thm)], [c_456, c_24])).
% 5.44/2.09  tff(c_770, plain, (![B_209]: (~r1_tarski(k4_orders_2('#skF_7', '#skF_8'), B_209) | r2_hidden(k1_xboole_0, B_209))), inference(negUnitSimplification, [status(thm)], [c_730, c_466])).
% 5.44/2.09  tff(c_866, plain, (![B_217, C_218]: (r2_hidden(k1_xboole_0, k4_xboole_0(B_217, k1_tarski(C_218))) | r2_hidden(C_218, k4_orders_2('#skF_7', '#skF_8')) | ~r1_tarski(k4_orders_2('#skF_7', '#skF_8'), B_217))), inference(resolution, [status(thm)], [c_38, c_770])).
% 5.44/2.09  tff(c_885, plain, (![C_218]: (r2_hidden(k1_xboole_0, k1_xboole_0) | r2_hidden(C_218, k4_orders_2('#skF_7', '#skF_8')) | ~r1_tarski(k4_orders_2('#skF_7', '#skF_8'), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_866])).
% 5.44/2.09  tff(c_893, plain, (![C_218]: (r2_hidden(C_218, k4_orders_2('#skF_7', '#skF_8')) | ~r1_tarski(k4_orders_2('#skF_7', '#skF_8'), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_234, c_885])).
% 5.44/2.09  tff(c_894, plain, (~r1_tarski(k4_orders_2('#skF_7', '#skF_8'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_893])).
% 5.44/2.09  tff(c_1000, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_999, c_894])).
% 5.44/2.09  tff(c_1011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1000])).
% 5.44/2.09  tff(c_1012, plain, (![A_198, B_156]: (k2_xboole_0(k4_orders_2('#skF_7', '#skF_8'), A_198)!=k2_xboole_0(B_156, k1_xboole_0) | r2_hidden(k1_xboole_0, B_156))), inference(splitRight, [status(thm)], [c_704])).
% 5.44/2.09  tff(c_1196, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_7', '#skF_8'))), inference(reflexivity, [status(thm), theory('equality')], [c_1012])).
% 5.44/2.09  tff(c_50, plain, (![D_67, A_46, B_58]: (m2_orders_2(D_67, A_46, B_58) | ~r2_hidden(D_67, k4_orders_2(A_46, B_58)) | ~m1_orders_1(B_58, k1_orders_1(u1_struct_0(A_46))) | ~l1_orders_2(A_46) | ~v5_orders_2(A_46) | ~v4_orders_2(A_46) | ~v3_orders_2(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.44/2.09  tff(c_1216, plain, (m2_orders_2(k1_xboole_0, '#skF_7', '#skF_8') | ~m1_orders_1('#skF_8', k1_orders_1(u1_struct_0('#skF_7'))) | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_1196, c_50])).
% 5.44/2.09  tff(c_1233, plain, (m2_orders_2(k1_xboole_0, '#skF_7', '#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_1216])).
% 5.44/2.09  tff(c_1234, plain, (m2_orders_2(k1_xboole_0, '#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_80, c_1233])).
% 5.44/2.09  tff(c_1013, plain, (k4_orders_2('#skF_7', '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_704])).
% 5.44/2.09  tff(c_179, plain, (![B_112]: (k3_xboole_0(k1_xboole_0, B_112)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_160, c_18])).
% 5.44/2.09  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.44/2.09  tff(c_235, plain, (![C_117]: (~r2_hidden(C_117, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_201])).
% 5.44/2.09  tff(c_246, plain, (![B_2]: (r1_xboole_0(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_235])).
% 5.44/2.09  tff(c_1651, plain, (![A_305, B_306, C_307]: (m2_orders_2('#skF_4'(A_305, B_306, C_307), A_305, B_306) | r2_hidden('#skF_5'(A_305, B_306, C_307), C_307) | k4_orders_2(A_305, B_306)=C_307 | ~m1_orders_1(B_306, k1_orders_1(u1_struct_0(A_305))) | ~l1_orders_2(A_305) | ~v5_orders_2(A_305) | ~v4_orders_2(A_305) | ~v3_orders_2(A_305) | v2_struct_0(A_305))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.44/2.09  tff(c_1653, plain, (![C_307]: (m2_orders_2('#skF_4'('#skF_7', '#skF_8', C_307), '#skF_7', '#skF_8') | r2_hidden('#skF_5'('#skF_7', '#skF_8', C_307), C_307) | k4_orders_2('#skF_7', '#skF_8')=C_307 | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_1651])).
% 5.44/2.09  tff(c_1656, plain, (![C_307]: (m2_orders_2('#skF_4'('#skF_7', '#skF_8', C_307), '#skF_7', '#skF_8') | r2_hidden('#skF_5'('#skF_7', '#skF_8', C_307), C_307) | k4_orders_2('#skF_7', '#skF_8')=C_307 | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_1653])).
% 5.44/2.09  tff(c_1698, plain, (![C_313]: (m2_orders_2('#skF_4'('#skF_7', '#skF_8', C_313), '#skF_7', '#skF_8') | r2_hidden('#skF_5'('#skF_7', '#skF_8', C_313), C_313) | k4_orders_2('#skF_7', '#skF_8')=C_313)), inference(negUnitSimplification, [status(thm)], [c_80, c_1656])).
% 5.44/2.09  tff(c_1975, plain, (![A_333, B_334]: (~r1_xboole_0(A_333, B_334) | m2_orders_2('#skF_4'('#skF_7', '#skF_8', k3_xboole_0(A_333, B_334)), '#skF_7', '#skF_8') | k4_orders_2('#skF_7', '#skF_8')=k3_xboole_0(A_333, B_334))), inference(resolution, [status(thm)], [c_1698, c_10])).
% 5.44/2.09  tff(c_1978, plain, (![B_112]: (~r1_xboole_0(k1_xboole_0, B_112) | m2_orders_2('#skF_4'('#skF_7', '#skF_8', k1_xboole_0), '#skF_7', '#skF_8') | k4_orders_2('#skF_7', '#skF_8')=k3_xboole_0(k1_xboole_0, B_112))), inference(superposition, [status(thm), theory('equality')], [c_179, c_1975])).
% 5.44/2.09  tff(c_1980, plain, (m2_orders_2('#skF_4'('#skF_7', '#skF_8', k1_xboole_0), '#skF_7', '#skF_8') | k4_orders_2('#skF_7', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_179, c_246, c_1978])).
% 5.44/2.09  tff(c_1981, plain, (m2_orders_2('#skF_4'('#skF_7', '#skF_8', k1_xboole_0), '#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1013, c_1980])).
% 5.44/2.09  tff(c_1253, plain, (![C_249, D_250, A_251, B_252]: (~r1_xboole_0(C_249, D_250) | ~m2_orders_2(D_250, A_251, B_252) | ~m2_orders_2(C_249, A_251, B_252) | ~m1_orders_1(B_252, k1_orders_1(u1_struct_0(A_251))) | ~l1_orders_2(A_251) | ~v5_orders_2(A_251) | ~v4_orders_2(A_251) | ~v3_orders_2(A_251) | v2_struct_0(A_251))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.44/2.09  tff(c_2941, plain, (![A_424, B_425, A_426]: (~m2_orders_2(k1_xboole_0, A_424, B_425) | ~m2_orders_2(A_426, A_424, B_425) | ~m1_orders_1(B_425, k1_orders_1(u1_struct_0(A_424))) | ~l1_orders_2(A_424) | ~v5_orders_2(A_424) | ~v4_orders_2(A_424) | ~v3_orders_2(A_424) | v2_struct_0(A_424))), inference(resolution, [status(thm)], [c_22, c_1253])).
% 5.44/2.09  tff(c_2947, plain, (~m2_orders_2(k1_xboole_0, '#skF_7', '#skF_8') | ~m1_orders_1('#skF_8', k1_orders_1(u1_struct_0('#skF_7'))) | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_1981, c_2941])).
% 5.44/2.09  tff(c_2968, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_1234, c_2947])).
% 5.44/2.09  tff(c_2970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2968])).
% 5.44/2.09  tff(c_2972, plain, (r1_tarski(k4_orders_2('#skF_7', '#skF_8'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_893])).
% 5.44/2.09  tff(c_769, plain, (![B_161]: (~r1_tarski(k4_orders_2('#skF_7', '#skF_8'), B_161) | r2_hidden(k1_xboole_0, B_161))), inference(negUnitSimplification, [status(thm)], [c_730, c_466])).
% 5.44/2.09  tff(c_2997, plain, (r2_hidden(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_2972, c_769])).
% 5.44/2.09  tff(c_3006, plain, $false, inference(negUnitSimplification, [status(thm)], [c_234, c_2997])).
% 5.44/2.09  tff(c_3007, plain, (![B_113]: (~r1_xboole_0(k1_xboole_0, B_113))), inference(splitRight, [status(thm)], [c_201])).
% 5.44/2.09  tff(c_120, plain, (![A_97, B_98]: (r1_xboole_0(k4_xboole_0(A_97, B_98), k4_xboole_0(B_98, A_97)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.44/2.09  tff(c_123, plain, (![A_16]: (r1_xboole_0(k1_xboole_0, k4_xboole_0(A_16, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_120])).
% 5.44/2.09  tff(c_3009, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3007, c_123])).
% 5.44/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.44/2.09  
% 5.44/2.09  Inference rules
% 5.44/2.09  ----------------------
% 5.44/2.09  #Ref     : 11
% 5.44/2.09  #Sup     : 734
% 5.44/2.09  #Fact    : 0
% 5.44/2.09  #Define  : 0
% 5.44/2.09  #Split   : 5
% 5.44/2.09  #Chain   : 0
% 5.44/2.09  #Close   : 0
% 5.44/2.09  
% 5.44/2.09  Ordering : KBO
% 5.44/2.09  
% 5.44/2.09  Simplification rules
% 5.44/2.09  ----------------------
% 5.44/2.09  #Subsume      : 139
% 5.44/2.09  #Demod        : 320
% 5.44/2.09  #Tautology    : 151
% 5.44/2.09  #SimpNegUnit  : 25
% 5.44/2.09  #BackRed      : 29
% 5.44/2.09  
% 5.44/2.09  #Partial instantiations: 0
% 5.44/2.09  #Strategies tried      : 1
% 5.44/2.09  
% 5.44/2.09  Timing (in seconds)
% 5.44/2.09  ----------------------
% 5.44/2.09  Preprocessing        : 0.38
% 5.44/2.09  Parsing              : 0.19
% 5.44/2.09  CNF conversion       : 0.03
% 5.44/2.09  Main loop            : 0.92
% 5.44/2.09  Inferencing          : 0.30
% 5.44/2.09  Reduction            : 0.29
% 5.44/2.09  Demodulation         : 0.20
% 5.44/2.09  BG Simplification    : 0.04
% 5.44/2.09  Subsumption          : 0.20
% 5.44/2.09  Abstraction          : 0.05
% 5.44/2.09  MUC search           : 0.00
% 5.44/2.09  Cooper               : 0.00
% 5.44/2.09  Total                : 1.34
% 5.44/2.09  Index Insertion      : 0.00
% 5.44/2.09  Index Deletion       : 0.00
% 5.44/2.09  Index Matching       : 0.00
% 5.44/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
