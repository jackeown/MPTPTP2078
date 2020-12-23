%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:50 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 188 expanded)
%              Number of leaves         :   32 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :  121 ( 553 expanded)
%              Number of equality atoms :   39 ( 134 expanded)
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

tff(f_109,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_89,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_77,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( k7_relset_1(A_44,B_45,C_46,D_47) = k9_relat_1(C_46,D_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_80,plain,(
    ! [D_47] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_47) = k9_relat_1('#skF_5',D_47) ),
    inference(resolution,[status(thm)],[c_48,c_77])).

tff(c_38,plain,(
    ~ r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_81,plain,(
    ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_38])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_58])).

tff(c_64,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_61])).

tff(c_44,plain,(
    r2_hidden('#skF_7','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_65,plain,(
    ! [A_35,B_36,C_37] :
      ( k1_relset_1(A_35,B_36,C_37) = k1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_69,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_191,plain,(
    ! [B_86,A_87,C_88] :
      ( k1_xboole_0 = B_86
      | k1_relset_1(A_87,B_86,C_88) = A_87
      | ~ v1_funct_2(C_88,A_87,B_86)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_194,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_191])).

tff(c_197,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_69,c_194])).

tff(c_198,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_197])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_40,plain,(
    k1_funct_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_20,plain,(
    ! [A_12,B_15] :
      ( k1_funct_1(A_12,B_15) = k1_xboole_0
      | r2_hidden(B_15,k1_relat_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_95,plain,(
    ! [B_59,A_60] :
      ( r2_hidden(k4_tarski(B_59,k1_funct_1(A_60,B_59)),A_60)
      | ~ r2_hidden(B_59,k1_relat_1(A_60))
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_98,plain,
    ( r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_95])).

tff(c_100,plain,
    ( r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_52,c_98])).

tff(c_101,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_105,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_xboole_0
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_101])).

tff(c_108,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_52,c_40,c_105])).

tff(c_114,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_46])).

tff(c_36,plain,(
    ! [B_25,A_24,C_26] :
      ( k1_xboole_0 = B_25
      | k1_relset_1(A_24,B_25,C_26) = A_24
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_154,plain,(
    ! [B_78,A_79,C_80] :
      ( B_78 = '#skF_6'
      | k1_relset_1(A_79,B_78,C_80) = A_79
      | ~ v1_funct_2(C_80,A_79,B_78)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_36])).

tff(c_157,plain,
    ( '#skF_6' = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_154])).

tff(c_160,plain,
    ( '#skF_6' = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_69,c_157])).

tff(c_161,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_160])).

tff(c_162,plain,(
    ~ r2_hidden('#skF_7','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_101])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_162])).

tff(c_167,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_42,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_236,plain,(
    ! [A_95,C_96,B_97,D_98] :
      ( r2_hidden(A_95,k9_relat_1(C_96,B_97))
      | ~ r2_hidden(D_98,B_97)
      | ~ r2_hidden(k4_tarski(D_98,A_95),C_96)
      | ~ r2_hidden(D_98,k1_relat_1(C_96))
      | ~ v1_relat_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_267,plain,(
    ! [A_99,C_100] :
      ( r2_hidden(A_99,k9_relat_1(C_100,'#skF_4'))
      | ~ r2_hidden(k4_tarski('#skF_7',A_99),C_100)
      | ~ r2_hidden('#skF_7',k1_relat_1(C_100))
      | ~ v1_relat_1(C_100) ) ),
    inference(resolution,[status(thm)],[c_42,c_236])).

tff(c_274,plain,
    ( r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_167,c_267])).

tff(c_286,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_44,c_198,c_274])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:46:19 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.35  
% 2.22/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.35  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.22/1.35  
% 2.22/1.35  %Foreground sorts:
% 2.22/1.35  
% 2.22/1.35  
% 2.22/1.35  %Background operators:
% 2.22/1.35  
% 2.22/1.35  
% 2.22/1.35  %Foreground operators:
% 2.22/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.22/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.22/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.22/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.22/1.35  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.22/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.22/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.22/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.22/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.22/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.22/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.22/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.35  
% 2.22/1.36  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: ((?[F]: ((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))) => r2_hidden(E, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_2)).
% 2.22/1.36  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.22/1.36  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.22/1.36  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.22/1.36  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.22/1.36  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.22/1.36  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 2.22/1.36  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.22/1.36  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.22/1.36  tff(c_77, plain, (![A_44, B_45, C_46, D_47]: (k7_relset_1(A_44, B_45, C_46, D_47)=k9_relat_1(C_46, D_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.22/1.36  tff(c_80, plain, (![D_47]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_47)=k9_relat_1('#skF_5', D_47))), inference(resolution, [status(thm)], [c_48, c_77])).
% 2.22/1.36  tff(c_38, plain, (~r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.22/1.36  tff(c_81, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_38])).
% 2.22/1.36  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.22/1.36  tff(c_58, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.22/1.36  tff(c_61, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_58])).
% 2.22/1.36  tff(c_64, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_61])).
% 2.22/1.36  tff(c_44, plain, (r2_hidden('#skF_7', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.22/1.36  tff(c_46, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.22/1.36  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.22/1.36  tff(c_65, plain, (![A_35, B_36, C_37]: (k1_relset_1(A_35, B_36, C_37)=k1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.22/1.36  tff(c_69, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_65])).
% 2.22/1.36  tff(c_191, plain, (![B_86, A_87, C_88]: (k1_xboole_0=B_86 | k1_relset_1(A_87, B_86, C_88)=A_87 | ~v1_funct_2(C_88, A_87, B_86) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.22/1.36  tff(c_194, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_191])).
% 2.22/1.36  tff(c_197, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_69, c_194])).
% 2.22/1.36  tff(c_198, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_46, c_197])).
% 2.22/1.36  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.22/1.36  tff(c_40, plain, (k1_funct_1('#skF_5', '#skF_7')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.22/1.36  tff(c_20, plain, (![A_12, B_15]: (k1_funct_1(A_12, B_15)=k1_xboole_0 | r2_hidden(B_15, k1_relat_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.22/1.36  tff(c_95, plain, (![B_59, A_60]: (r2_hidden(k4_tarski(B_59, k1_funct_1(A_60, B_59)), A_60) | ~r2_hidden(B_59, k1_relat_1(A_60)) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.22/1.36  tff(c_98, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_40, c_95])).
% 2.22/1.36  tff(c_100, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_52, c_98])).
% 2.22/1.36  tff(c_101, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_100])).
% 2.22/1.36  tff(c_105, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_101])).
% 2.22/1.36  tff(c_108, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_52, c_40, c_105])).
% 2.22/1.36  tff(c_114, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_46])).
% 2.22/1.36  tff(c_36, plain, (![B_25, A_24, C_26]: (k1_xboole_0=B_25 | k1_relset_1(A_24, B_25, C_26)=A_24 | ~v1_funct_2(C_26, A_24, B_25) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.22/1.36  tff(c_154, plain, (![B_78, A_79, C_80]: (B_78='#skF_6' | k1_relset_1(A_79, B_78, C_80)=A_79 | ~v1_funct_2(C_80, A_79, B_78) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_36])).
% 2.22/1.36  tff(c_157, plain, ('#skF_6'='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_154])).
% 2.22/1.36  tff(c_160, plain, ('#skF_6'='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_69, c_157])).
% 2.22/1.36  tff(c_161, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_114, c_160])).
% 2.22/1.36  tff(c_162, plain, (~r2_hidden('#skF_7', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_101])).
% 2.22/1.36  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_162])).
% 2.22/1.36  tff(c_167, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_100])).
% 2.22/1.36  tff(c_42, plain, (r2_hidden('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.22/1.36  tff(c_236, plain, (![A_95, C_96, B_97, D_98]: (r2_hidden(A_95, k9_relat_1(C_96, B_97)) | ~r2_hidden(D_98, B_97) | ~r2_hidden(k4_tarski(D_98, A_95), C_96) | ~r2_hidden(D_98, k1_relat_1(C_96)) | ~v1_relat_1(C_96))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.22/1.36  tff(c_267, plain, (![A_99, C_100]: (r2_hidden(A_99, k9_relat_1(C_100, '#skF_4')) | ~r2_hidden(k4_tarski('#skF_7', A_99), C_100) | ~r2_hidden('#skF_7', k1_relat_1(C_100)) | ~v1_relat_1(C_100))), inference(resolution, [status(thm)], [c_42, c_236])).
% 2.22/1.36  tff(c_274, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_167, c_267])).
% 2.22/1.36  tff(c_286, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_44, c_198, c_274])).
% 2.22/1.36  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_286])).
% 2.22/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.36  
% 2.22/1.36  Inference rules
% 2.22/1.36  ----------------------
% 2.22/1.36  #Ref     : 0
% 2.22/1.36  #Sup     : 46
% 2.22/1.36  #Fact    : 0
% 2.22/1.36  #Define  : 0
% 2.22/1.36  #Split   : 2
% 2.22/1.36  #Chain   : 0
% 2.22/1.36  #Close   : 0
% 2.22/1.36  
% 2.22/1.36  Ordering : KBO
% 2.22/1.36  
% 2.22/1.36  Simplification rules
% 2.22/1.36  ----------------------
% 2.22/1.36  #Subsume      : 2
% 2.22/1.36  #Demod        : 55
% 2.22/1.36  #Tautology    : 19
% 2.22/1.36  #SimpNegUnit  : 5
% 2.22/1.36  #BackRed      : 11
% 2.22/1.36  
% 2.22/1.36  #Partial instantiations: 0
% 2.22/1.36  #Strategies tried      : 1
% 2.22/1.36  
% 2.22/1.36  Timing (in seconds)
% 2.22/1.36  ----------------------
% 2.22/1.36  Preprocessing        : 0.29
% 2.22/1.36  Parsing              : 0.15
% 2.22/1.37  CNF conversion       : 0.02
% 2.22/1.37  Main loop            : 0.22
% 2.22/1.37  Inferencing          : 0.08
% 2.22/1.37  Reduction            : 0.07
% 2.22/1.37  Demodulation         : 0.05
% 2.22/1.37  BG Simplification    : 0.02
% 2.22/1.37  Subsumption          : 0.04
% 2.22/1.37  Abstraction          : 0.01
% 2.22/1.37  MUC search           : 0.00
% 2.22/1.37  Cooper               : 0.00
% 2.22/1.37  Total                : 0.55
% 2.22/1.37  Index Insertion      : 0.00
% 2.22/1.37  Index Deletion       : 0.00
% 2.22/1.37  Index Matching       : 0.00
% 2.22/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
