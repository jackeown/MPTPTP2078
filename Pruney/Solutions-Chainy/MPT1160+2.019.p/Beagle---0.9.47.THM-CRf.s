%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:46 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   61 (  71 expanded)
%              Number of leaves         :   32 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  154 ( 211 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k4_mcart_1 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_orders_2(A,k1_struct_0(A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_20,plain,(
    ! [A_30] :
      ( l1_struct_0(A_30)
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    ! [A_50] :
      ( k1_struct_0(A_50) = k1_xboole_0
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_49,plain,(
    ! [A_51] :
      ( k1_struct_0(A_51) = k1_xboole_0
      | ~ l1_orders_2(A_51) ) ),
    inference(resolution,[status(thm)],[c_20,c_44])).

tff(c_53,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_49])).

tff(c_28,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_54,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_28])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_38,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_36,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    ! [A_79,B_80,C_81] :
      ( m1_subset_1(k3_orders_2(A_79,B_80,C_81),k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_subset_1(C_81,u1_struct_0(A_79))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_orders_2(A_79)
      | ~ v5_orders_2(A_79)
      | ~ v4_orders_2(A_79)
      | ~ v3_orders_2(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    ! [A_82,A_83,B_84,C_85] :
      ( m1_subset_1(A_82,u1_struct_0(A_83))
      | ~ r2_hidden(A_82,k3_orders_2(A_83,B_84,C_85))
      | ~ m1_subset_1(C_85,u1_struct_0(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_orders_2(A_83)
      | ~ v5_orders_2(A_83)
      | ~ v4_orders_2(A_83)
      | ~ v3_orders_2(A_83)
      | v2_struct_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_92,c_6])).

tff(c_100,plain,(
    ! [A_83,B_84,C_85] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_83,B_84,C_85)),u1_struct_0(A_83))
      | ~ m1_subset_1(C_85,u1_struct_0(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_orders_2(A_83)
      | ~ v5_orders_2(A_83)
      | ~ v4_orders_2(A_83)
      | ~ v3_orders_2(A_83)
      | v2_struct_0(A_83)
      | k3_orders_2(A_83,B_84,C_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_96])).

tff(c_101,plain,(
    ! [B_86,D_87,A_88,C_89] :
      ( r2_hidden(B_86,D_87)
      | ~ r2_hidden(B_86,k3_orders_2(A_88,D_87,C_89))
      | ~ m1_subset_1(D_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(C_89,u1_struct_0(A_88))
      | ~ m1_subset_1(B_86,u1_struct_0(A_88))
      | ~ l1_orders_2(A_88)
      | ~ v5_orders_2(A_88)
      | ~ v4_orders_2(A_88)
      | ~ v3_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_147,plain,(
    ! [A_107,D_108,C_109] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_107,D_108,C_109)),D_108)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_subset_1(C_109,u1_struct_0(A_107))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_107,D_108,C_109)),u1_struct_0(A_107))
      | ~ l1_orders_2(A_107)
      | ~ v5_orders_2(A_107)
      | ~ v4_orders_2(A_107)
      | ~ v3_orders_2(A_107)
      | v2_struct_0(A_107)
      | k3_orders_2(A_107,D_108,C_109) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_101])).

tff(c_151,plain,(
    ! [A_110,B_111,C_112] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_110,B_111,C_112)),B_111)
      | ~ m1_subset_1(C_112,u1_struct_0(A_110))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110)
      | k3_orders_2(A_110,B_111,C_112) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_100,c_147])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_209,plain,(
    ! [B_125,A_126,C_127] :
      ( ~ r1_tarski(B_125,'#skF_1'(k3_orders_2(A_126,B_125,C_127)))
      | ~ m1_subset_1(C_127,u1_struct_0(A_126))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_orders_2(A_126)
      | ~ v5_orders_2(A_126)
      | ~ v4_orders_2(A_126)
      | ~ v3_orders_2(A_126)
      | v2_struct_0(A_126)
      | k3_orders_2(A_126,B_125,C_127) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_151,c_8])).

tff(c_213,plain,(
    ! [C_127,A_126] :
      ( ~ m1_subset_1(C_127,u1_struct_0(A_126))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_orders_2(A_126)
      | ~ v5_orders_2(A_126)
      | ~ v4_orders_2(A_126)
      | ~ v3_orders_2(A_126)
      | v2_struct_0(A_126)
      | k3_orders_2(A_126,k1_xboole_0,C_127) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_209])).

tff(c_217,plain,(
    ! [C_128,A_129] :
      ( ~ m1_subset_1(C_128,u1_struct_0(A_129))
      | ~ l1_orders_2(A_129)
      | ~ v5_orders_2(A_129)
      | ~ v4_orders_2(A_129)
      | ~ v3_orders_2(A_129)
      | v2_struct_0(A_129)
      | k3_orders_2(A_129,k1_xboole_0,C_128) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_213])).

tff(c_223,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_217])).

tff(c_227,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_223])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_40,c_227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:58:34 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.30  
% 2.53/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.31  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k4_mcart_1 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.53/1.31  
% 2.53/1.31  %Foreground sorts:
% 2.53/1.31  
% 2.53/1.31  
% 2.53/1.31  %Background operators:
% 2.53/1.31  
% 2.53/1.31  
% 2.53/1.31  %Foreground operators:
% 2.53/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.53/1.31  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.53/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.53/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.31  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.53/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.31  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.53/1.31  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.53/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.53/1.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.53/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.31  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.53/1.31  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.53/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.53/1.31  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.53/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.31  
% 2.53/1.32  tff(f_124, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_orders_2)).
% 2.53/1.32  tff(f_81, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.53/1.32  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 2.53/1.32  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.53/1.32  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.53/1.32  tff(f_56, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 2.53/1.32  tff(f_77, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.53/1.32  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.53/1.32  tff(f_107, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 2.53/1.32  tff(f_40, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.53/1.32  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.53/1.32  tff(c_20, plain, (![A_30]: (l1_struct_0(A_30) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.53/1.32  tff(c_44, plain, (![A_50]: (k1_struct_0(A_50)=k1_xboole_0 | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.53/1.32  tff(c_49, plain, (![A_51]: (k1_struct_0(A_51)=k1_xboole_0 | ~l1_orders_2(A_51))), inference(resolution, [status(thm)], [c_20, c_44])).
% 2.53/1.32  tff(c_53, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_49])).
% 2.53/1.32  tff(c_28, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.53/1.32  tff(c_54, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_53, c_28])).
% 2.53/1.32  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.53/1.32  tff(c_38, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.53/1.32  tff(c_36, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.53/1.32  tff(c_34, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.53/1.32  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.53/1.32  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.32  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.53/1.32  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.53/1.32  tff(c_92, plain, (![A_79, B_80, C_81]: (m1_subset_1(k3_orders_2(A_79, B_80, C_81), k1_zfmisc_1(u1_struct_0(A_79))) | ~m1_subset_1(C_81, u1_struct_0(A_79)) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_orders_2(A_79) | ~v5_orders_2(A_79) | ~v4_orders_2(A_79) | ~v3_orders_2(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.53/1.32  tff(c_6, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.53/1.32  tff(c_96, plain, (![A_82, A_83, B_84, C_85]: (m1_subset_1(A_82, u1_struct_0(A_83)) | ~r2_hidden(A_82, k3_orders_2(A_83, B_84, C_85)) | ~m1_subset_1(C_85, u1_struct_0(A_83)) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_orders_2(A_83) | ~v5_orders_2(A_83) | ~v4_orders_2(A_83) | ~v3_orders_2(A_83) | v2_struct_0(A_83))), inference(resolution, [status(thm)], [c_92, c_6])).
% 2.53/1.32  tff(c_100, plain, (![A_83, B_84, C_85]: (m1_subset_1('#skF_1'(k3_orders_2(A_83, B_84, C_85)), u1_struct_0(A_83)) | ~m1_subset_1(C_85, u1_struct_0(A_83)) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_orders_2(A_83) | ~v5_orders_2(A_83) | ~v4_orders_2(A_83) | ~v3_orders_2(A_83) | v2_struct_0(A_83) | k3_orders_2(A_83, B_84, C_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_96])).
% 2.53/1.32  tff(c_101, plain, (![B_86, D_87, A_88, C_89]: (r2_hidden(B_86, D_87) | ~r2_hidden(B_86, k3_orders_2(A_88, D_87, C_89)) | ~m1_subset_1(D_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(C_89, u1_struct_0(A_88)) | ~m1_subset_1(B_86, u1_struct_0(A_88)) | ~l1_orders_2(A_88) | ~v5_orders_2(A_88) | ~v4_orders_2(A_88) | ~v3_orders_2(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.53/1.32  tff(c_147, plain, (![A_107, D_108, C_109]: (r2_hidden('#skF_1'(k3_orders_2(A_107, D_108, C_109)), D_108) | ~m1_subset_1(D_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~m1_subset_1(C_109, u1_struct_0(A_107)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_107, D_108, C_109)), u1_struct_0(A_107)) | ~l1_orders_2(A_107) | ~v5_orders_2(A_107) | ~v4_orders_2(A_107) | ~v3_orders_2(A_107) | v2_struct_0(A_107) | k3_orders_2(A_107, D_108, C_109)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_101])).
% 2.53/1.32  tff(c_151, plain, (![A_110, B_111, C_112]: (r2_hidden('#skF_1'(k3_orders_2(A_110, B_111, C_112)), B_111) | ~m1_subset_1(C_112, u1_struct_0(A_110)) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110) | k3_orders_2(A_110, B_111, C_112)=k1_xboole_0)), inference(resolution, [status(thm)], [c_100, c_147])).
% 2.53/1.32  tff(c_8, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.53/1.32  tff(c_209, plain, (![B_125, A_126, C_127]: (~r1_tarski(B_125, '#skF_1'(k3_orders_2(A_126, B_125, C_127))) | ~m1_subset_1(C_127, u1_struct_0(A_126)) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_orders_2(A_126) | ~v5_orders_2(A_126) | ~v4_orders_2(A_126) | ~v3_orders_2(A_126) | v2_struct_0(A_126) | k3_orders_2(A_126, B_125, C_127)=k1_xboole_0)), inference(resolution, [status(thm)], [c_151, c_8])).
% 2.53/1.32  tff(c_213, plain, (![C_127, A_126]: (~m1_subset_1(C_127, u1_struct_0(A_126)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_orders_2(A_126) | ~v5_orders_2(A_126) | ~v4_orders_2(A_126) | ~v3_orders_2(A_126) | v2_struct_0(A_126) | k3_orders_2(A_126, k1_xboole_0, C_127)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_209])).
% 2.53/1.32  tff(c_217, plain, (![C_128, A_129]: (~m1_subset_1(C_128, u1_struct_0(A_129)) | ~l1_orders_2(A_129) | ~v5_orders_2(A_129) | ~v4_orders_2(A_129) | ~v3_orders_2(A_129) | v2_struct_0(A_129) | k3_orders_2(A_129, k1_xboole_0, C_128)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_213])).
% 2.53/1.32  tff(c_223, plain, (~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_217])).
% 2.53/1.32  tff(c_227, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_223])).
% 2.53/1.32  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_40, c_227])).
% 2.53/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.32  
% 2.53/1.32  Inference rules
% 2.53/1.32  ----------------------
% 2.53/1.32  #Ref     : 0
% 2.53/1.32  #Sup     : 39
% 2.53/1.32  #Fact    : 0
% 2.53/1.32  #Define  : 0
% 2.53/1.32  #Split   : 0
% 2.53/1.32  #Chain   : 0
% 2.53/1.32  #Close   : 0
% 2.53/1.32  
% 2.53/1.32  Ordering : KBO
% 2.53/1.32  
% 2.53/1.32  Simplification rules
% 2.53/1.32  ----------------------
% 2.53/1.32  #Subsume      : 5
% 2.53/1.32  #Demod        : 11
% 2.53/1.32  #Tautology    : 6
% 2.53/1.32  #SimpNegUnit  : 1
% 2.53/1.32  #BackRed      : 1
% 2.53/1.32  
% 2.53/1.32  #Partial instantiations: 0
% 2.53/1.32  #Strategies tried      : 1
% 2.53/1.32  
% 2.53/1.32  Timing (in seconds)
% 2.53/1.32  ----------------------
% 2.53/1.33  Preprocessing        : 0.30
% 2.53/1.33  Parsing              : 0.17
% 2.53/1.33  CNF conversion       : 0.02
% 2.53/1.33  Main loop            : 0.25
% 2.53/1.33  Inferencing          : 0.10
% 2.53/1.33  Reduction            : 0.06
% 2.53/1.33  Demodulation         : 0.04
% 2.53/1.33  BG Simplification    : 0.02
% 2.53/1.33  Subsumption          : 0.06
% 2.53/1.33  Abstraction          : 0.01
% 2.53/1.33  MUC search           : 0.00
% 2.53/1.33  Cooper               : 0.00
% 2.53/1.33  Total                : 0.58
% 2.53/1.33  Index Insertion      : 0.00
% 2.53/1.33  Index Deletion       : 0.00
% 2.53/1.33  Index Matching       : 0.00
% 2.53/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
