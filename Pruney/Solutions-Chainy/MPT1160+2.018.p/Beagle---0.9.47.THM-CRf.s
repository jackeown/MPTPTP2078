%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:45 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   61 (  71 expanded)
%              Number of leaves         :   32 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :  146 ( 203 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_126,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_79,axiom,(
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

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_109,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_36,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_24,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_69,plain,(
    ! [A_44] :
      ( k1_struct_0(A_44) = k1_xboole_0
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_89,plain,(
    ! [A_49] :
      ( k1_struct_0(A_49) = k1_xboole_0
      | ~ l1_orders_2(A_49) ) ),
    inference(resolution,[status(thm)],[c_24,c_69])).

tff(c_93,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_89])).

tff(c_32,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_94,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_32])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_38,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_1'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_124,plain,(
    ! [A_65,B_66,C_67] :
      ( m1_subset_1(k3_orders_2(A_65,B_66,C_67),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(C_67,u1_struct_0(A_65))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_orders_2(A_65)
      | ~ v5_orders_2(A_65)
      | ~ v4_orders_2(A_65)
      | ~ v3_orders_2(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7] :
      ( m1_subset_1(A_6,C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_128,plain,(
    ! [A_68,A_69,B_70,C_71] :
      ( m1_subset_1(A_68,u1_struct_0(A_69))
      | ~ r2_hidden(A_68,k3_orders_2(A_69,B_70,C_71))
      | ~ m1_subset_1(C_71,u1_struct_0(A_69))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_orders_2(A_69)
      | ~ v5_orders_2(A_69)
      | ~ v4_orders_2(A_69)
      | ~ v3_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_124,c_12])).

tff(c_132,plain,(
    ! [A_69,B_70,C_71] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_69,B_70,C_71)),u1_struct_0(A_69))
      | ~ m1_subset_1(C_71,u1_struct_0(A_69))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_orders_2(A_69)
      | ~ v5_orders_2(A_69)
      | ~ v4_orders_2(A_69)
      | ~ v3_orders_2(A_69)
      | v2_struct_0(A_69)
      | k3_orders_2(A_69,B_70,C_71) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_128])).

tff(c_133,plain,(
    ! [B_72,D_73,A_74,C_75] :
      ( r2_hidden(B_72,D_73)
      | ~ r2_hidden(B_72,k3_orders_2(A_74,D_73,C_75))
      | ~ m1_subset_1(D_73,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(C_75,u1_struct_0(A_74))
      | ~ m1_subset_1(B_72,u1_struct_0(A_74))
      | ~ l1_orders_2(A_74)
      | ~ v5_orders_2(A_74)
      | ~ v4_orders_2(A_74)
      | ~ v3_orders_2(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_152,plain,(
    ! [A_87,D_88,C_89] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_87,D_88,C_89)),D_88)
      | ~ m1_subset_1(D_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1(C_89,u1_struct_0(A_87))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_87,D_88,C_89)),u1_struct_0(A_87))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87)
      | k3_orders_2(A_87,D_88,C_89) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_133])).

tff(c_156,plain,(
    ! [A_90,B_91,C_92] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_90,B_91,C_92)),B_91)
      | ~ m1_subset_1(C_92,u1_struct_0(A_90))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_orders_2(A_90)
      | ~ v5_orders_2(A_90)
      | ~ v4_orders_2(A_90)
      | ~ v3_orders_2(A_90)
      | v2_struct_0(A_90)
      | k3_orders_2(A_90,B_91,C_92) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_132,c_152])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_45,B_46] : ~ r2_hidden(A_45,k2_zfmisc_1(A_45,B_46)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_80,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_74])).

tff(c_173,plain,(
    ! [C_92,A_90] :
      ( ~ m1_subset_1(C_92,u1_struct_0(A_90))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_orders_2(A_90)
      | ~ v5_orders_2(A_90)
      | ~ v4_orders_2(A_90)
      | ~ v3_orders_2(A_90)
      | v2_struct_0(A_90)
      | k3_orders_2(A_90,k1_xboole_0,C_92) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_156,c_80])).

tff(c_182,plain,(
    ! [C_93,A_94] :
      ( ~ m1_subset_1(C_93,u1_struct_0(A_94))
      | ~ l1_orders_2(A_94)
      | ~ v5_orders_2(A_94)
      | ~ v4_orders_2(A_94)
      | ~ v3_orders_2(A_94)
      | v2_struct_0(A_94)
      | k3_orders_2(A_94,k1_xboole_0,C_93) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_173])).

tff(c_188,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_182])).

tff(c_192,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_188])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_44,c_192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:28:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.28  
% 2.27/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.28  %$ r2_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.27/1.28  
% 2.27/1.28  %Foreground sorts:
% 2.27/1.28  
% 2.27/1.28  
% 2.27/1.28  %Background operators:
% 2.27/1.28  
% 2.27/1.28  
% 2.27/1.28  %Foreground operators:
% 2.27/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.27/1.28  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.27/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.27/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.28  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.27/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.27/1.28  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.27/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.27/1.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.28  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.27/1.28  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.27/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.27/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.28  
% 2.27/1.29  tff(f_126, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_orders_2)).
% 2.27/1.29  tff(f_83, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.27/1.29  tff(f_62, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 2.27/1.29  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.27/1.29  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.27/1.29  tff(f_79, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.27/1.29  tff(f_42, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.27/1.29  tff(f_109, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 2.27/1.29  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.27/1.29  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.27/1.29  tff(c_36, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.27/1.29  tff(c_24, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.27/1.29  tff(c_69, plain, (![A_44]: (k1_struct_0(A_44)=k1_xboole_0 | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.27/1.29  tff(c_89, plain, (![A_49]: (k1_struct_0(A_49)=k1_xboole_0 | ~l1_orders_2(A_49))), inference(resolution, [status(thm)], [c_24, c_69])).
% 2.27/1.29  tff(c_93, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_89])).
% 2.27/1.29  tff(c_32, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.27/1.29  tff(c_94, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_93, c_32])).
% 2.27/1.29  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.27/1.29  tff(c_42, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.27/1.29  tff(c_40, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.27/1.29  tff(c_38, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.27/1.29  tff(c_34, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.27/1.29  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.27/1.29  tff(c_14, plain, (![A_9]: (r2_hidden('#skF_1'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.27/1.29  tff(c_124, plain, (![A_65, B_66, C_67]: (m1_subset_1(k3_orders_2(A_65, B_66, C_67), k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_subset_1(C_67, u1_struct_0(A_65)) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_orders_2(A_65) | ~v5_orders_2(A_65) | ~v4_orders_2(A_65) | ~v3_orders_2(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.27/1.29  tff(c_12, plain, (![A_6, C_8, B_7]: (m1_subset_1(A_6, C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.27/1.29  tff(c_128, plain, (![A_68, A_69, B_70, C_71]: (m1_subset_1(A_68, u1_struct_0(A_69)) | ~r2_hidden(A_68, k3_orders_2(A_69, B_70, C_71)) | ~m1_subset_1(C_71, u1_struct_0(A_69)) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_orders_2(A_69) | ~v5_orders_2(A_69) | ~v4_orders_2(A_69) | ~v3_orders_2(A_69) | v2_struct_0(A_69))), inference(resolution, [status(thm)], [c_124, c_12])).
% 2.27/1.29  tff(c_132, plain, (![A_69, B_70, C_71]: (m1_subset_1('#skF_1'(k3_orders_2(A_69, B_70, C_71)), u1_struct_0(A_69)) | ~m1_subset_1(C_71, u1_struct_0(A_69)) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_orders_2(A_69) | ~v5_orders_2(A_69) | ~v4_orders_2(A_69) | ~v3_orders_2(A_69) | v2_struct_0(A_69) | k3_orders_2(A_69, B_70, C_71)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_128])).
% 2.27/1.29  tff(c_133, plain, (![B_72, D_73, A_74, C_75]: (r2_hidden(B_72, D_73) | ~r2_hidden(B_72, k3_orders_2(A_74, D_73, C_75)) | ~m1_subset_1(D_73, k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(C_75, u1_struct_0(A_74)) | ~m1_subset_1(B_72, u1_struct_0(A_74)) | ~l1_orders_2(A_74) | ~v5_orders_2(A_74) | ~v4_orders_2(A_74) | ~v3_orders_2(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.27/1.29  tff(c_152, plain, (![A_87, D_88, C_89]: (r2_hidden('#skF_1'(k3_orders_2(A_87, D_88, C_89)), D_88) | ~m1_subset_1(D_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_subset_1(C_89, u1_struct_0(A_87)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_87, D_88, C_89)), u1_struct_0(A_87)) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87) | k3_orders_2(A_87, D_88, C_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_133])).
% 2.27/1.29  tff(c_156, plain, (![A_90, B_91, C_92]: (r2_hidden('#skF_1'(k3_orders_2(A_90, B_91, C_92)), B_91) | ~m1_subset_1(C_92, u1_struct_0(A_90)) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_orders_2(A_90) | ~v5_orders_2(A_90) | ~v4_orders_2(A_90) | ~v3_orders_2(A_90) | v2_struct_0(A_90) | k3_orders_2(A_90, B_91, C_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_132, c_152])).
% 2.27/1.29  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.29  tff(c_74, plain, (![A_45, B_46]: (~r2_hidden(A_45, k2_zfmisc_1(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.27/1.29  tff(c_80, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_74])).
% 2.27/1.29  tff(c_173, plain, (![C_92, A_90]: (~m1_subset_1(C_92, u1_struct_0(A_90)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_orders_2(A_90) | ~v5_orders_2(A_90) | ~v4_orders_2(A_90) | ~v3_orders_2(A_90) | v2_struct_0(A_90) | k3_orders_2(A_90, k1_xboole_0, C_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_156, c_80])).
% 2.27/1.29  tff(c_182, plain, (![C_93, A_94]: (~m1_subset_1(C_93, u1_struct_0(A_94)) | ~l1_orders_2(A_94) | ~v5_orders_2(A_94) | ~v4_orders_2(A_94) | ~v3_orders_2(A_94) | v2_struct_0(A_94) | k3_orders_2(A_94, k1_xboole_0, C_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_173])).
% 2.27/1.29  tff(c_188, plain, (~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_182])).
% 2.27/1.29  tff(c_192, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_188])).
% 2.27/1.29  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_44, c_192])).
% 2.27/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.29  
% 2.27/1.29  Inference rules
% 2.27/1.29  ----------------------
% 2.27/1.29  #Ref     : 0
% 2.27/1.29  #Sup     : 33
% 2.27/1.29  #Fact    : 0
% 2.27/1.29  #Define  : 0
% 2.27/1.29  #Split   : 0
% 2.27/1.29  #Chain   : 0
% 2.27/1.29  #Close   : 0
% 2.27/1.29  
% 2.27/1.29  Ordering : KBO
% 2.27/1.29  
% 2.27/1.29  Simplification rules
% 2.27/1.29  ----------------------
% 2.27/1.29  #Subsume      : 4
% 2.27/1.29  #Demod        : 6
% 2.27/1.29  #Tautology    : 11
% 2.27/1.29  #SimpNegUnit  : 1
% 2.27/1.29  #BackRed      : 1
% 2.27/1.29  
% 2.27/1.29  #Partial instantiations: 0
% 2.27/1.29  #Strategies tried      : 1
% 2.27/1.29  
% 2.27/1.29  Timing (in seconds)
% 2.27/1.29  ----------------------
% 2.27/1.30  Preprocessing        : 0.30
% 2.27/1.30  Parsing              : 0.17
% 2.27/1.30  CNF conversion       : 0.02
% 2.27/1.30  Main loop            : 0.22
% 2.27/1.30  Inferencing          : 0.09
% 2.27/1.30  Reduction            : 0.06
% 2.27/1.30  Demodulation         : 0.04
% 2.27/1.30  BG Simplification    : 0.02
% 2.27/1.30  Subsumption          : 0.05
% 2.27/1.30  Abstraction          : 0.01
% 2.27/1.30  MUC search           : 0.00
% 2.27/1.30  Cooper               : 0.00
% 2.27/1.30  Total                : 0.56
% 2.27/1.30  Index Insertion      : 0.00
% 2.27/1.30  Index Deletion       : 0.00
% 2.27/1.30  Index Matching       : 0.00
% 2.27/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
