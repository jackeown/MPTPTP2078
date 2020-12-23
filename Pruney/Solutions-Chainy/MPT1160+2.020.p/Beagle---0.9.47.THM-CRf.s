%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:46 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   61 (  71 expanded)
%              Number of leaves         :   32 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  157 ( 217 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_129,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_orders_2(A,k1_struct_0(A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_orders_2)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_112,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_30,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_18,plain,(
    ! [A_34] :
      ( l1_struct_0(A_34)
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    ! [A_54] :
      ( k1_struct_0(A_54) = k1_xboole_0
      | ~ l1_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_47,plain,(
    ! [A_55] :
      ( k1_struct_0(A_55) = k1_xboole_0
      | ~ l1_orders_2(A_55) ) ),
    inference(resolution,[status(thm)],[c_18,c_42])).

tff(c_51,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_47])).

tff(c_26,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_52,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_26])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_36,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_34,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_32,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_95,plain,(
    ! [A_80,B_81,C_82] :
      ( m1_subset_1(k3_orders_2(A_80,B_81,C_82),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ m1_subset_1(C_82,u1_struct_0(A_80))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_orders_2(A_80)
      | ~ v5_orders_2(A_80)
      | ~ v4_orders_2(A_80)
      | ~ v3_orders_2(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_104,plain,(
    ! [A_86,A_87,B_88,C_89] :
      ( m1_subset_1(A_86,u1_struct_0(A_87))
      | ~ r2_hidden(A_86,k3_orders_2(A_87,B_88,C_89))
      | ~ m1_subset_1(C_89,u1_struct_0(A_87))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_95,c_6])).

tff(c_108,plain,(
    ! [A_87,B_88,C_89] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_87,B_88,C_89)),u1_struct_0(A_87))
      | ~ m1_subset_1(C_89,u1_struct_0(A_87))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87)
      | k3_orders_2(A_87,B_88,C_89) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_104])).

tff(c_109,plain,(
    ! [B_90,D_91,A_92,C_93] :
      ( r2_hidden(B_90,D_91)
      | ~ r2_hidden(B_90,k3_orders_2(A_92,D_91,C_93))
      | ~ m1_subset_1(D_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m1_subset_1(C_93,u1_struct_0(A_92))
      | ~ m1_subset_1(B_90,u1_struct_0(A_92))
      | ~ l1_orders_2(A_92)
      | ~ v5_orders_2(A_92)
      | ~ v4_orders_2(A_92)
      | ~ v3_orders_2(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_156,plain,(
    ! [A_114,D_115,C_116] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_114,D_115,C_116)),D_115)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ m1_subset_1(C_116,u1_struct_0(A_114))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_114,D_115,C_116)),u1_struct_0(A_114))
      | ~ l1_orders_2(A_114)
      | ~ v5_orders_2(A_114)
      | ~ v4_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114)
      | k3_orders_2(A_114,D_115,C_116) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_109])).

tff(c_160,plain,(
    ! [A_117,B_118,C_119] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_117,B_118,C_119)),B_118)
      | ~ m1_subset_1(C_119,u1_struct_0(A_117))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_orders_2(A_117)
      | ~ v5_orders_2(A_117)
      | ~ v4_orders_2(A_117)
      | ~ v3_orders_2(A_117)
      | v2_struct_0(A_117)
      | k3_orders_2(A_117,B_118,C_119) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_108,c_156])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_233,plain,(
    ! [B_132,A_133,C_134] :
      ( ~ r1_tarski(B_132,'#skF_1'(k3_orders_2(A_133,B_132,C_134)))
      | ~ m1_subset_1(C_134,u1_struct_0(A_133))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_orders_2(A_133)
      | ~ v5_orders_2(A_133)
      | ~ v4_orders_2(A_133)
      | ~ v3_orders_2(A_133)
      | v2_struct_0(A_133)
      | k3_orders_2(A_133,B_132,C_134) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_160,c_8])).

tff(c_237,plain,(
    ! [C_134,A_133] :
      ( ~ m1_subset_1(C_134,u1_struct_0(A_133))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_orders_2(A_133)
      | ~ v5_orders_2(A_133)
      | ~ v4_orders_2(A_133)
      | ~ v3_orders_2(A_133)
      | v2_struct_0(A_133)
      | k3_orders_2(A_133,k1_xboole_0,C_134) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_233])).

tff(c_241,plain,(
    ! [C_135,A_136] :
      ( ~ m1_subset_1(C_135,u1_struct_0(A_136))
      | ~ l1_orders_2(A_136)
      | ~ v5_orders_2(A_136)
      | ~ v4_orders_2(A_136)
      | ~ v3_orders_2(A_136)
      | v2_struct_0(A_136)
      | k3_orders_2(A_136,k1_xboole_0,C_135) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_237])).

tff(c_247,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_241])).

tff(c_251,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_247])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38,c_251])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.46  
% 2.48/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.46  %$ r2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.48/1.46  
% 2.48/1.46  %Foreground sorts:
% 2.48/1.46  
% 2.48/1.46  
% 2.48/1.46  %Background operators:
% 2.48/1.46  
% 2.48/1.46  
% 2.48/1.46  %Foreground operators:
% 2.48/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.48/1.46  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.48/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.48/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.46  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.48/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.48/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.46  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.48/1.46  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.48/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.48/1.46  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.48/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.46  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.48/1.46  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.48/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.48/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.46  
% 2.88/1.48  tff(f_129, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_orders_2)).
% 2.88/1.48  tff(f_86, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.88/1.48  tff(f_65, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 2.88/1.48  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.88/1.48  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.88/1.48  tff(f_61, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.88/1.48  tff(f_82, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.88/1.48  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.88/1.48  tff(f_112, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 2.88/1.48  tff(f_40, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.88/1.48  tff(c_30, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.88/1.48  tff(c_18, plain, (![A_34]: (l1_struct_0(A_34) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.88/1.48  tff(c_42, plain, (![A_54]: (k1_struct_0(A_54)=k1_xboole_0 | ~l1_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.88/1.48  tff(c_47, plain, (![A_55]: (k1_struct_0(A_55)=k1_xboole_0 | ~l1_orders_2(A_55))), inference(resolution, [status(thm)], [c_18, c_42])).
% 2.88/1.48  tff(c_51, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_47])).
% 2.88/1.48  tff(c_26, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.88/1.48  tff(c_52, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_51, c_26])).
% 2.88/1.48  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.88/1.48  tff(c_36, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.88/1.48  tff(c_34, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.88/1.48  tff(c_32, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.88/1.48  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.88/1.48  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.88/1.48  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.88/1.48  tff(c_12, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.88/1.48  tff(c_95, plain, (![A_80, B_81, C_82]: (m1_subset_1(k3_orders_2(A_80, B_81, C_82), k1_zfmisc_1(u1_struct_0(A_80))) | ~m1_subset_1(C_82, u1_struct_0(A_80)) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_orders_2(A_80) | ~v5_orders_2(A_80) | ~v4_orders_2(A_80) | ~v3_orders_2(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.88/1.48  tff(c_6, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.88/1.48  tff(c_104, plain, (![A_86, A_87, B_88, C_89]: (m1_subset_1(A_86, u1_struct_0(A_87)) | ~r2_hidden(A_86, k3_orders_2(A_87, B_88, C_89)) | ~m1_subset_1(C_89, u1_struct_0(A_87)) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_95, c_6])).
% 2.88/1.48  tff(c_108, plain, (![A_87, B_88, C_89]: (m1_subset_1('#skF_1'(k3_orders_2(A_87, B_88, C_89)), u1_struct_0(A_87)) | ~m1_subset_1(C_89, u1_struct_0(A_87)) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87) | k3_orders_2(A_87, B_88, C_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_104])).
% 2.88/1.48  tff(c_109, plain, (![B_90, D_91, A_92, C_93]: (r2_hidden(B_90, D_91) | ~r2_hidden(B_90, k3_orders_2(A_92, D_91, C_93)) | ~m1_subset_1(D_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~m1_subset_1(C_93, u1_struct_0(A_92)) | ~m1_subset_1(B_90, u1_struct_0(A_92)) | ~l1_orders_2(A_92) | ~v5_orders_2(A_92) | ~v4_orders_2(A_92) | ~v3_orders_2(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.88/1.48  tff(c_156, plain, (![A_114, D_115, C_116]: (r2_hidden('#skF_1'(k3_orders_2(A_114, D_115, C_116)), D_115) | ~m1_subset_1(D_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~m1_subset_1(C_116, u1_struct_0(A_114)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_114, D_115, C_116)), u1_struct_0(A_114)) | ~l1_orders_2(A_114) | ~v5_orders_2(A_114) | ~v4_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114) | k3_orders_2(A_114, D_115, C_116)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_109])).
% 2.88/1.48  tff(c_160, plain, (![A_117, B_118, C_119]: (r2_hidden('#skF_1'(k3_orders_2(A_117, B_118, C_119)), B_118) | ~m1_subset_1(C_119, u1_struct_0(A_117)) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_orders_2(A_117) | ~v5_orders_2(A_117) | ~v4_orders_2(A_117) | ~v3_orders_2(A_117) | v2_struct_0(A_117) | k3_orders_2(A_117, B_118, C_119)=k1_xboole_0)), inference(resolution, [status(thm)], [c_108, c_156])).
% 2.88/1.48  tff(c_8, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.48  tff(c_233, plain, (![B_132, A_133, C_134]: (~r1_tarski(B_132, '#skF_1'(k3_orders_2(A_133, B_132, C_134))) | ~m1_subset_1(C_134, u1_struct_0(A_133)) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_orders_2(A_133) | ~v5_orders_2(A_133) | ~v4_orders_2(A_133) | ~v3_orders_2(A_133) | v2_struct_0(A_133) | k3_orders_2(A_133, B_132, C_134)=k1_xboole_0)), inference(resolution, [status(thm)], [c_160, c_8])).
% 2.88/1.48  tff(c_237, plain, (![C_134, A_133]: (~m1_subset_1(C_134, u1_struct_0(A_133)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_orders_2(A_133) | ~v5_orders_2(A_133) | ~v4_orders_2(A_133) | ~v3_orders_2(A_133) | v2_struct_0(A_133) | k3_orders_2(A_133, k1_xboole_0, C_134)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_233])).
% 2.88/1.48  tff(c_241, plain, (![C_135, A_136]: (~m1_subset_1(C_135, u1_struct_0(A_136)) | ~l1_orders_2(A_136) | ~v5_orders_2(A_136) | ~v4_orders_2(A_136) | ~v3_orders_2(A_136) | v2_struct_0(A_136) | k3_orders_2(A_136, k1_xboole_0, C_135)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_237])).
% 2.88/1.48  tff(c_247, plain, (~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_241])).
% 2.88/1.48  tff(c_251, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_247])).
% 2.88/1.48  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_38, c_251])).
% 2.88/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.48  
% 2.88/1.48  Inference rules
% 2.88/1.48  ----------------------
% 2.88/1.48  #Ref     : 0
% 2.88/1.48  #Sup     : 43
% 2.88/1.48  #Fact    : 0
% 2.88/1.48  #Define  : 0
% 2.88/1.48  #Split   : 0
% 2.88/1.48  #Chain   : 0
% 2.88/1.48  #Close   : 0
% 2.88/1.48  
% 2.88/1.48  Ordering : KBO
% 2.88/1.48  
% 2.88/1.48  Simplification rules
% 2.88/1.48  ----------------------
% 2.88/1.48  #Subsume      : 5
% 2.88/1.48  #Demod        : 11
% 2.88/1.48  #Tautology    : 6
% 2.88/1.48  #SimpNegUnit  : 1
% 2.88/1.48  #BackRed      : 1
% 2.88/1.48  
% 2.88/1.48  #Partial instantiations: 0
% 2.88/1.48  #Strategies tried      : 1
% 2.88/1.48  
% 2.88/1.48  Timing (in seconds)
% 2.88/1.48  ----------------------
% 2.88/1.48  Preprocessing        : 0.35
% 2.88/1.48  Parsing              : 0.19
% 2.88/1.48  CNF conversion       : 0.03
% 2.88/1.48  Main loop            : 0.28
% 2.88/1.48  Inferencing          : 0.12
% 2.88/1.48  Reduction            : 0.07
% 2.88/1.48  Demodulation         : 0.05
% 2.88/1.48  BG Simplification    : 0.02
% 2.88/1.48  Subsumption          : 0.06
% 2.88/1.48  Abstraction          : 0.01
% 2.88/1.48  MUC search           : 0.00
% 2.88/1.48  Cooper               : 0.00
% 2.88/1.48  Total                : 0.67
% 2.88/1.48  Index Insertion      : 0.00
% 2.88/1.48  Index Deletion       : 0.00
% 2.88/1.48  Index Matching       : 0.00
% 2.88/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
