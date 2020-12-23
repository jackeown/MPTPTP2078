%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:46 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
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
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > k4_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

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
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    ! [A_42] :
      ( k1_struct_0(A_42) = k1_xboole_0
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_49,plain,(
    ! [A_43] :
      ( k1_struct_0(A_43) = k1_xboole_0
      | ~ l1_orders_2(A_43) ) ),
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
    ! [A_63,B_64,C_65] :
      ( m1_subset_1(k3_orders_2(A_63,B_64,C_65),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_subset_1(C_65,u1_struct_0(A_63))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_orders_2(A_63)
      | ~ v5_orders_2(A_63)
      | ~ v4_orders_2(A_63)
      | ~ v3_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    ! [A_66,A_67,B_68,C_69] :
      ( m1_subset_1(A_66,u1_struct_0(A_67))
      | ~ r2_hidden(A_66,k3_orders_2(A_67,B_68,C_69))
      | ~ m1_subset_1(C_69,u1_struct_0(A_67))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_orders_2(A_67)
      | ~ v5_orders_2(A_67)
      | ~ v4_orders_2(A_67)
      | ~ v3_orders_2(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_92,c_6])).

tff(c_100,plain,(
    ! [A_67,B_68,C_69] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_67,B_68,C_69)),u1_struct_0(A_67))
      | ~ m1_subset_1(C_69,u1_struct_0(A_67))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_orders_2(A_67)
      | ~ v5_orders_2(A_67)
      | ~ v4_orders_2(A_67)
      | ~ v3_orders_2(A_67)
      | v2_struct_0(A_67)
      | k3_orders_2(A_67,B_68,C_69) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_96])).

tff(c_101,plain,(
    ! [B_70,D_71,A_72,C_73] :
      ( r2_hidden(B_70,D_71)
      | ~ r2_hidden(B_70,k3_orders_2(A_72,D_71,C_73))
      | ~ m1_subset_1(D_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_subset_1(C_73,u1_struct_0(A_72))
      | ~ m1_subset_1(B_70,u1_struct_0(A_72))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_149,plain,(
    ! [A_99,D_100,C_101] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_99,D_100,C_101)),D_100)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(C_101,u1_struct_0(A_99))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_99,D_100,C_101)),u1_struct_0(A_99))
      | ~ l1_orders_2(A_99)
      | ~ v5_orders_2(A_99)
      | ~ v4_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99)
      | k3_orders_2(A_99,D_100,C_101) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_101])).

tff(c_153,plain,(
    ! [A_102,B_103,C_104] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_102,B_103,C_104)),B_103)
      | ~ m1_subset_1(C_104,u1_struct_0(A_102))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_orders_2(A_102)
      | ~ v5_orders_2(A_102)
      | ~ v4_orders_2(A_102)
      | ~ v3_orders_2(A_102)
      | v2_struct_0(A_102)
      | k3_orders_2(A_102,B_103,C_104) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_100,c_149])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_211,plain,(
    ! [B_117,A_118,C_119] :
      ( ~ r1_tarski(B_117,'#skF_1'(k3_orders_2(A_118,B_117,C_119)))
      | ~ m1_subset_1(C_119,u1_struct_0(A_118))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_orders_2(A_118)
      | ~ v5_orders_2(A_118)
      | ~ v4_orders_2(A_118)
      | ~ v3_orders_2(A_118)
      | v2_struct_0(A_118)
      | k3_orders_2(A_118,B_117,C_119) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_153,c_8])).

tff(c_215,plain,(
    ! [C_119,A_118] :
      ( ~ m1_subset_1(C_119,u1_struct_0(A_118))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_orders_2(A_118)
      | ~ v5_orders_2(A_118)
      | ~ v4_orders_2(A_118)
      | ~ v3_orders_2(A_118)
      | v2_struct_0(A_118)
      | k3_orders_2(A_118,k1_xboole_0,C_119) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_211])).

tff(c_219,plain,(
    ! [C_120,A_121] :
      ( ~ m1_subset_1(C_120,u1_struct_0(A_121))
      | ~ l1_orders_2(A_121)
      | ~ v5_orders_2(A_121)
      | ~ v4_orders_2(A_121)
      | ~ v3_orders_2(A_121)
      | v2_struct_0(A_121)
      | k3_orders_2(A_121,k1_xboole_0,C_120) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_215])).

tff(c_225,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_219])).

tff(c_229,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_225])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_40,c_229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:07:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.36  
% 2.51/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.36  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > k4_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.51/1.36  
% 2.51/1.36  %Foreground sorts:
% 2.51/1.36  
% 2.51/1.36  
% 2.51/1.36  %Background operators:
% 2.51/1.36  
% 2.51/1.36  
% 2.51/1.36  %Foreground operators:
% 2.51/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.51/1.36  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.51/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.51/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.51/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.36  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.51/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.36  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.51/1.36  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.51/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.51/1.36  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.51/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.36  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.51/1.36  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.51/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.51/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.36  
% 2.51/1.38  tff(f_124, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_orders_2)).
% 2.51/1.38  tff(f_81, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.51/1.38  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 2.51/1.38  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.51/1.38  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.51/1.38  tff(f_56, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.51/1.38  tff(f_77, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.51/1.38  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.51/1.38  tff(f_107, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 2.51/1.38  tff(f_40, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.51/1.38  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.51/1.38  tff(c_20, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.51/1.38  tff(c_44, plain, (![A_42]: (k1_struct_0(A_42)=k1_xboole_0 | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.51/1.38  tff(c_49, plain, (![A_43]: (k1_struct_0(A_43)=k1_xboole_0 | ~l1_orders_2(A_43))), inference(resolution, [status(thm)], [c_20, c_44])).
% 2.51/1.38  tff(c_53, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_49])).
% 2.51/1.38  tff(c_28, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.51/1.38  tff(c_54, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_53, c_28])).
% 2.51/1.38  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.51/1.38  tff(c_38, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.51/1.38  tff(c_36, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.51/1.38  tff(c_34, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.51/1.38  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.51/1.38  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.38  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.38  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.38  tff(c_92, plain, (![A_63, B_64, C_65]: (m1_subset_1(k3_orders_2(A_63, B_64, C_65), k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_subset_1(C_65, u1_struct_0(A_63)) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_orders_2(A_63) | ~v5_orders_2(A_63) | ~v4_orders_2(A_63) | ~v3_orders_2(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.51/1.38  tff(c_6, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.38  tff(c_96, plain, (![A_66, A_67, B_68, C_69]: (m1_subset_1(A_66, u1_struct_0(A_67)) | ~r2_hidden(A_66, k3_orders_2(A_67, B_68, C_69)) | ~m1_subset_1(C_69, u1_struct_0(A_67)) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_orders_2(A_67) | ~v5_orders_2(A_67) | ~v4_orders_2(A_67) | ~v3_orders_2(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_92, c_6])).
% 2.51/1.38  tff(c_100, plain, (![A_67, B_68, C_69]: (m1_subset_1('#skF_1'(k3_orders_2(A_67, B_68, C_69)), u1_struct_0(A_67)) | ~m1_subset_1(C_69, u1_struct_0(A_67)) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_orders_2(A_67) | ~v5_orders_2(A_67) | ~v4_orders_2(A_67) | ~v3_orders_2(A_67) | v2_struct_0(A_67) | k3_orders_2(A_67, B_68, C_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_96])).
% 2.51/1.38  tff(c_101, plain, (![B_70, D_71, A_72, C_73]: (r2_hidden(B_70, D_71) | ~r2_hidden(B_70, k3_orders_2(A_72, D_71, C_73)) | ~m1_subset_1(D_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~m1_subset_1(C_73, u1_struct_0(A_72)) | ~m1_subset_1(B_70, u1_struct_0(A_72)) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.51/1.38  tff(c_149, plain, (![A_99, D_100, C_101]: (r2_hidden('#skF_1'(k3_orders_2(A_99, D_100, C_101)), D_100) | ~m1_subset_1(D_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_subset_1(C_101, u1_struct_0(A_99)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_99, D_100, C_101)), u1_struct_0(A_99)) | ~l1_orders_2(A_99) | ~v5_orders_2(A_99) | ~v4_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99) | k3_orders_2(A_99, D_100, C_101)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_101])).
% 2.51/1.38  tff(c_153, plain, (![A_102, B_103, C_104]: (r2_hidden('#skF_1'(k3_orders_2(A_102, B_103, C_104)), B_103) | ~m1_subset_1(C_104, u1_struct_0(A_102)) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_orders_2(A_102) | ~v5_orders_2(A_102) | ~v4_orders_2(A_102) | ~v3_orders_2(A_102) | v2_struct_0(A_102) | k3_orders_2(A_102, B_103, C_104)=k1_xboole_0)), inference(resolution, [status(thm)], [c_100, c_149])).
% 2.51/1.38  tff(c_8, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.51/1.38  tff(c_211, plain, (![B_117, A_118, C_119]: (~r1_tarski(B_117, '#skF_1'(k3_orders_2(A_118, B_117, C_119))) | ~m1_subset_1(C_119, u1_struct_0(A_118)) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_orders_2(A_118) | ~v5_orders_2(A_118) | ~v4_orders_2(A_118) | ~v3_orders_2(A_118) | v2_struct_0(A_118) | k3_orders_2(A_118, B_117, C_119)=k1_xboole_0)), inference(resolution, [status(thm)], [c_153, c_8])).
% 2.51/1.38  tff(c_215, plain, (![C_119, A_118]: (~m1_subset_1(C_119, u1_struct_0(A_118)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_orders_2(A_118) | ~v5_orders_2(A_118) | ~v4_orders_2(A_118) | ~v3_orders_2(A_118) | v2_struct_0(A_118) | k3_orders_2(A_118, k1_xboole_0, C_119)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_211])).
% 2.51/1.38  tff(c_219, plain, (![C_120, A_121]: (~m1_subset_1(C_120, u1_struct_0(A_121)) | ~l1_orders_2(A_121) | ~v5_orders_2(A_121) | ~v4_orders_2(A_121) | ~v3_orders_2(A_121) | v2_struct_0(A_121) | k3_orders_2(A_121, k1_xboole_0, C_120)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_215])).
% 2.51/1.38  tff(c_225, plain, (~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_219])).
% 2.51/1.38  tff(c_229, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_225])).
% 2.51/1.38  tff(c_231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_40, c_229])).
% 2.51/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.38  
% 2.51/1.38  Inference rules
% 2.51/1.38  ----------------------
% 2.51/1.38  #Ref     : 0
% 2.51/1.38  #Sup     : 39
% 2.51/1.38  #Fact    : 0
% 2.51/1.38  #Define  : 0
% 2.51/1.38  #Split   : 0
% 2.51/1.38  #Chain   : 0
% 2.51/1.38  #Close   : 0
% 2.51/1.38  
% 2.51/1.38  Ordering : KBO
% 2.51/1.38  
% 2.51/1.38  Simplification rules
% 2.51/1.38  ----------------------
% 2.51/1.38  #Subsume      : 7
% 2.51/1.38  #Demod        : 11
% 2.51/1.38  #Tautology    : 6
% 2.51/1.38  #SimpNegUnit  : 1
% 2.51/1.38  #BackRed      : 1
% 2.51/1.38  
% 2.51/1.38  #Partial instantiations: 0
% 2.51/1.38  #Strategies tried      : 1
% 2.51/1.38  
% 2.51/1.38  Timing (in seconds)
% 2.51/1.38  ----------------------
% 2.51/1.38  Preprocessing        : 0.33
% 2.51/1.38  Parsing              : 0.19
% 2.51/1.38  CNF conversion       : 0.02
% 2.51/1.38  Main loop            : 0.26
% 2.51/1.38  Inferencing          : 0.11
% 2.51/1.38  Reduction            : 0.06
% 2.51/1.38  Demodulation         : 0.05
% 2.51/1.38  BG Simplification    : 0.02
% 2.51/1.38  Subsumption          : 0.06
% 2.51/1.38  Abstraction          : 0.01
% 2.51/1.38  MUC search           : 0.00
% 2.51/1.38  Cooper               : 0.00
% 2.51/1.38  Total                : 0.62
% 2.51/1.38  Index Insertion      : 0.00
% 2.51/1.38  Index Deletion       : 0.00
% 2.51/1.38  Index Matching       : 0.00
% 2.51/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
