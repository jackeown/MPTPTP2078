%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:51 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 120 expanded)
%              Number of leaves         :   32 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 320 expanded)
%              Number of equality atoms :   31 (  81 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( B != k1_xboole_0
         => ! [E] :
              ( ? [F] :
                  ( r2_hidden(F,A)
                  & r2_hidden(F,C)
                  & E = k1_funct_1(D,F) )
             => r2_hidden(E,k7_relset_1(A,B,D,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_77,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( k7_relset_1(A_49,B_50,C_51,D_52) = k9_relat_1(C_51,D_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    ! [D_52] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_52) = k9_relat_1('#skF_5',D_52) ),
    inference(resolution,[status(thm)],[c_46,c_77])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_81,plain,(
    ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_36])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    ! [B_31,A_32] :
      ( v1_relat_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_56])).

tff(c_62,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_42,plain,(
    r2_hidden('#skF_7','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_63,plain,(
    ! [A_33,B_34,C_35] :
      ( k1_relset_1(A_33,B_34,C_35) = k1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_63])).

tff(c_172,plain,(
    ! [B_74,A_75,C_76] :
      ( k1_xboole_0 = B_74
      | k1_relset_1(A_75,B_74,C_76) = A_75
      | ~ v1_funct_2(C_76,A_75,B_74)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_175,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_172])).

tff(c_178,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_67,c_175])).

tff(c_179,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_178])).

tff(c_132,plain,(
    ! [B_68,A_69,C_70] :
      ( k1_xboole_0 = B_68
      | k1_relset_1(A_69,B_68,C_70) = A_69
      | ~ v1_funct_2(C_70,A_69,B_68)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_135,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_132])).

tff(c_138,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_67,c_135])).

tff(c_139,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_138])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    k1_funct_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_103,plain,(
    ! [A_63,C_64] :
      ( r2_hidden(k4_tarski(A_63,k1_funct_1(C_64,A_63)),C_64)
      | ~ r2_hidden(A_63,k1_relat_1(C_64))
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_112,plain,
    ( r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_103])).

tff(c_117,plain,
    ( r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_112])).

tff(c_118,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_140,plain,(
    ~ r2_hidden('#skF_7','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_118])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_140])).

tff(c_145,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_40,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_204,plain,(
    ! [A_82,C_83,B_84,D_85] :
      ( r2_hidden(A_82,k9_relat_1(C_83,B_84))
      | ~ r2_hidden(D_85,B_84)
      | ~ r2_hidden(k4_tarski(D_85,A_82),C_83)
      | ~ r2_hidden(D_85,k1_relat_1(C_83))
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_229,plain,(
    ! [A_86,C_87] :
      ( r2_hidden(A_86,k9_relat_1(C_87,'#skF_4'))
      | ~ r2_hidden(k4_tarski('#skF_7',A_86),C_87)
      | ~ r2_hidden('#skF_7',k1_relat_1(C_87))
      | ~ v1_relat_1(C_87) ) ),
    inference(resolution,[status(thm)],[c_40,c_204])).

tff(c_232,plain,
    ( r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_145,c_229])).

tff(c_239,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_42,c_179,c_232])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:04:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.49  
% 2.46/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.49  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.46/1.49  
% 2.46/1.49  %Foreground sorts:
% 2.46/1.49  
% 2.46/1.49  
% 2.46/1.49  %Background operators:
% 2.46/1.49  
% 2.46/1.49  
% 2.46/1.49  %Foreground operators:
% 2.46/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.46/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.46/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.46/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.49  tff('#skF_7', type, '#skF_7': $i).
% 2.46/1.49  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.46/1.49  tff('#skF_5', type, '#skF_5': $i).
% 2.46/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.46/1.49  tff('#skF_6', type, '#skF_6': $i).
% 2.46/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.46/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.46/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.46/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.46/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.49  
% 2.59/1.50  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: ((?[F]: ((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))) => r2_hidden(E, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_2)).
% 2.59/1.50  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.59/1.50  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.59/1.50  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.59/1.50  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.59/1.50  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.59/1.50  tff(f_55, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.59/1.50  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.59/1.50  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.59/1.50  tff(c_77, plain, (![A_49, B_50, C_51, D_52]: (k7_relset_1(A_49, B_50, C_51, D_52)=k9_relat_1(C_51, D_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.59/1.50  tff(c_80, plain, (![D_52]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_52)=k9_relat_1('#skF_5', D_52))), inference(resolution, [status(thm)], [c_46, c_77])).
% 2.59/1.50  tff(c_36, plain, (~r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.59/1.50  tff(c_81, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_36])).
% 2.59/1.50  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.59/1.50  tff(c_56, plain, (![B_31, A_32]: (v1_relat_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.50  tff(c_59, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_56])).
% 2.59/1.50  tff(c_62, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_59])).
% 2.59/1.50  tff(c_42, plain, (r2_hidden('#skF_7', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.59/1.50  tff(c_44, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.59/1.50  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.59/1.50  tff(c_63, plain, (![A_33, B_34, C_35]: (k1_relset_1(A_33, B_34, C_35)=k1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.59/1.50  tff(c_67, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_63])).
% 2.59/1.50  tff(c_172, plain, (![B_74, A_75, C_76]: (k1_xboole_0=B_74 | k1_relset_1(A_75, B_74, C_76)=A_75 | ~v1_funct_2(C_76, A_75, B_74) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.59/1.50  tff(c_175, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_172])).
% 2.59/1.50  tff(c_178, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_67, c_175])).
% 2.59/1.50  tff(c_179, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_178])).
% 2.59/1.50  tff(c_132, plain, (![B_68, A_69, C_70]: (k1_xboole_0=B_68 | k1_relset_1(A_69, B_68, C_70)=A_69 | ~v1_funct_2(C_70, A_69, B_68) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.59/1.50  tff(c_135, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_132])).
% 2.59/1.50  tff(c_138, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_67, c_135])).
% 2.59/1.50  tff(c_139, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_138])).
% 2.59/1.50  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.59/1.50  tff(c_38, plain, (k1_funct_1('#skF_5', '#skF_7')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.59/1.50  tff(c_103, plain, (![A_63, C_64]: (r2_hidden(k4_tarski(A_63, k1_funct_1(C_64, A_63)), C_64) | ~r2_hidden(A_63, k1_relat_1(C_64)) | ~v1_funct_1(C_64) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.59/1.50  tff(c_112, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_38, c_103])).
% 2.59/1.50  tff(c_117, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_112])).
% 2.59/1.50  tff(c_118, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_117])).
% 2.59/1.50  tff(c_140, plain, (~r2_hidden('#skF_7', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_118])).
% 2.59/1.50  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_140])).
% 2.59/1.50  tff(c_145, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_117])).
% 2.59/1.50  tff(c_40, plain, (r2_hidden('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.59/1.50  tff(c_204, plain, (![A_82, C_83, B_84, D_85]: (r2_hidden(A_82, k9_relat_1(C_83, B_84)) | ~r2_hidden(D_85, B_84) | ~r2_hidden(k4_tarski(D_85, A_82), C_83) | ~r2_hidden(D_85, k1_relat_1(C_83)) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.59/1.50  tff(c_229, plain, (![A_86, C_87]: (r2_hidden(A_86, k9_relat_1(C_87, '#skF_4')) | ~r2_hidden(k4_tarski('#skF_7', A_86), C_87) | ~r2_hidden('#skF_7', k1_relat_1(C_87)) | ~v1_relat_1(C_87))), inference(resolution, [status(thm)], [c_40, c_204])).
% 2.59/1.50  tff(c_232, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_145, c_229])).
% 2.59/1.50  tff(c_239, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_42, c_179, c_232])).
% 2.59/1.50  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_239])).
% 2.59/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.50  
% 2.59/1.50  Inference rules
% 2.59/1.50  ----------------------
% 2.59/1.50  #Ref     : 0
% 2.59/1.50  #Sup     : 40
% 2.59/1.50  #Fact    : 0
% 2.59/1.50  #Define  : 0
% 2.59/1.50  #Split   : 1
% 2.59/1.50  #Chain   : 0
% 2.59/1.50  #Close   : 0
% 2.59/1.50  
% 2.59/1.50  Ordering : KBO
% 2.59/1.50  
% 2.59/1.50  Simplification rules
% 2.59/1.50  ----------------------
% 2.59/1.50  #Subsume      : 1
% 2.59/1.50  #Demod        : 26
% 2.59/1.50  #Tautology    : 16
% 2.59/1.50  #SimpNegUnit  : 4
% 2.59/1.50  #BackRed      : 5
% 2.59/1.50  
% 2.59/1.50  #Partial instantiations: 0
% 2.59/1.50  #Strategies tried      : 1
% 2.59/1.50  
% 2.59/1.50  Timing (in seconds)
% 2.59/1.50  ----------------------
% 2.59/1.50  Preprocessing        : 0.46
% 2.59/1.50  Parsing              : 0.27
% 2.59/1.50  CNF conversion       : 0.02
% 2.59/1.51  Main loop            : 0.20
% 2.59/1.51  Inferencing          : 0.07
% 2.59/1.51  Reduction            : 0.06
% 2.59/1.51  Demodulation         : 0.04
% 2.59/1.51  BG Simplification    : 0.02
% 2.59/1.51  Subsumption          : 0.03
% 2.59/1.51  Abstraction          : 0.01
% 2.59/1.51  MUC search           : 0.00
% 2.59/1.51  Cooper               : 0.00
% 2.59/1.51  Total                : 0.70
% 2.59/1.51  Index Insertion      : 0.00
% 2.59/1.51  Index Deletion       : 0.00
% 2.59/1.51  Index Matching       : 0.00
% 2.59/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
