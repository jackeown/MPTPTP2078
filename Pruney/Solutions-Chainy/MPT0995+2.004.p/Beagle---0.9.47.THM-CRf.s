%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:49 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 167 expanded)
%              Number of leaves         :   31 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 511 expanded)
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

tff(f_104,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
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

tff(f_54,axiom,(
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

tff(f_36,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_73,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( k7_relset_1(A_44,B_45,C_46,D_47) = k9_relat_1(C_46,D_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_76,plain,(
    ! [D_47] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_47) = k9_relat_1('#skF_5',D_47) ),
    inference(resolution,[status(thm)],[c_46,c_73])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_77,plain,(
    ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_36])).

tff(c_55,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_59,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_55])).

tff(c_42,plain,(
    r2_hidden('#skF_7','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_60,plain,(
    ! [A_32,B_33,C_34] :
      ( k1_relset_1(A_32,B_33,C_34) = k1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_64,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_60])).

tff(c_160,plain,(
    ! [B_73,A_74,C_75] :
      ( k1_xboole_0 = B_73
      | k1_relset_1(A_74,B_73,C_75) = A_74
      | ~ v1_funct_2(C_75,A_74,B_73)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_163,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_160])).

tff(c_166,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_64,c_163])).

tff(c_167,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_166])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,(
    k1_funct_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_16,plain,(
    ! [A_7,B_10] :
      ( k1_funct_1(A_7,B_10) = k1_xboole_0
      | r2_hidden(B_10,k1_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_90,plain,(
    ! [B_55,A_56] :
      ( r2_hidden(k4_tarski(B_55,k1_funct_1(A_56,B_55)),A_56)
      | ~ r2_hidden(B_55,k1_relat_1(A_56))
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_93,plain,
    ( r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_90])).

tff(c_95,plain,
    ( r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_50,c_93])).

tff(c_96,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_99,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_xboole_0
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_96])).

tff(c_102,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_50,c_38,c_99])).

tff(c_109,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_44])).

tff(c_34,plain,(
    ! [B_23,A_22,C_24] :
      ( k1_xboole_0 = B_23
      | k1_relset_1(A_22,B_23,C_24) = A_22
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_116,plain,(
    ! [B_61,A_62,C_63] :
      ( B_61 = '#skF_6'
      | k1_relset_1(A_62,B_61,C_63) = A_62
      | ~ v1_funct_2(C_63,A_62,B_61)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_34])).

tff(c_119,plain,
    ( '#skF_6' = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_116])).

tff(c_122,plain,
    ( '#skF_6' = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_64,c_119])).

tff(c_123,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_122])).

tff(c_124,plain,(
    ~ r2_hidden('#skF_7','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_96])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_124])).

tff(c_129,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_40,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_197,plain,(
    ! [A_79,C_80,B_81,D_82] :
      ( r2_hidden(A_79,k9_relat_1(C_80,B_81))
      | ~ r2_hidden(D_82,B_81)
      | ~ r2_hidden(k4_tarski(D_82,A_79),C_80)
      | ~ r2_hidden(D_82,k1_relat_1(C_80))
      | ~ v1_relat_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_228,plain,(
    ! [A_83,C_84] :
      ( r2_hidden(A_83,k9_relat_1(C_84,'#skF_4'))
      | ~ r2_hidden(k4_tarski('#skF_7',A_83),C_84)
      | ~ r2_hidden('#skF_7',k1_relat_1(C_84))
      | ~ v1_relat_1(C_84) ) ),
    inference(resolution,[status(thm)],[c_40,c_197])).

tff(c_235,plain,
    ( r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_129,c_228])).

tff(c_247,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_42,c_167,c_235])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:27:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.30  
% 2.16/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.16/1.31  
% 2.16/1.31  %Foreground sorts:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Background operators:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Foreground operators:
% 2.16/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.16/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.16/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.16/1.31  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.16/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.16/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.16/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.16/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.16/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.31  
% 2.16/1.32  tff(f_104, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: ((?[F]: ((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))) => r2_hidden(E, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_2)).
% 2.16/1.32  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.16/1.32  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.16/1.32  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.16/1.32  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.16/1.32  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 2.16/1.32  tff(f_36, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.16/1.32  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.16/1.32  tff(c_73, plain, (![A_44, B_45, C_46, D_47]: (k7_relset_1(A_44, B_45, C_46, D_47)=k9_relat_1(C_46, D_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.16/1.32  tff(c_76, plain, (![D_47]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_47)=k9_relat_1('#skF_5', D_47))), inference(resolution, [status(thm)], [c_46, c_73])).
% 2.16/1.32  tff(c_36, plain, (~r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.16/1.32  tff(c_77, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_36])).
% 2.16/1.32  tff(c_55, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.16/1.32  tff(c_59, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_55])).
% 2.16/1.32  tff(c_42, plain, (r2_hidden('#skF_7', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.16/1.32  tff(c_44, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.16/1.32  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.16/1.32  tff(c_60, plain, (![A_32, B_33, C_34]: (k1_relset_1(A_32, B_33, C_34)=k1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.16/1.32  tff(c_64, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_60])).
% 2.16/1.32  tff(c_160, plain, (![B_73, A_74, C_75]: (k1_xboole_0=B_73 | k1_relset_1(A_74, B_73, C_75)=A_74 | ~v1_funct_2(C_75, A_74, B_73) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.16/1.32  tff(c_163, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_160])).
% 2.16/1.32  tff(c_166, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_64, c_163])).
% 2.16/1.32  tff(c_167, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_166])).
% 2.16/1.32  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.16/1.32  tff(c_38, plain, (k1_funct_1('#skF_5', '#skF_7')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.16/1.32  tff(c_16, plain, (![A_7, B_10]: (k1_funct_1(A_7, B_10)=k1_xboole_0 | r2_hidden(B_10, k1_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.16/1.32  tff(c_90, plain, (![B_55, A_56]: (r2_hidden(k4_tarski(B_55, k1_funct_1(A_56, B_55)), A_56) | ~r2_hidden(B_55, k1_relat_1(A_56)) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.16/1.32  tff(c_93, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_38, c_90])).
% 2.16/1.32  tff(c_95, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_50, c_93])).
% 2.16/1.32  tff(c_96, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_95])).
% 2.16/1.32  tff(c_99, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_96])).
% 2.16/1.32  tff(c_102, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_50, c_38, c_99])).
% 2.16/1.32  tff(c_109, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_44])).
% 2.16/1.32  tff(c_34, plain, (![B_23, A_22, C_24]: (k1_xboole_0=B_23 | k1_relset_1(A_22, B_23, C_24)=A_22 | ~v1_funct_2(C_24, A_22, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.16/1.32  tff(c_116, plain, (![B_61, A_62, C_63]: (B_61='#skF_6' | k1_relset_1(A_62, B_61, C_63)=A_62 | ~v1_funct_2(C_63, A_62, B_61) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_34])).
% 2.16/1.32  tff(c_119, plain, ('#skF_6'='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_116])).
% 2.16/1.32  tff(c_122, plain, ('#skF_6'='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_64, c_119])).
% 2.16/1.32  tff(c_123, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_109, c_122])).
% 2.16/1.32  tff(c_124, plain, (~r2_hidden('#skF_7', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_96])).
% 2.16/1.32  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_124])).
% 2.16/1.32  tff(c_129, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_95])).
% 2.16/1.32  tff(c_40, plain, (r2_hidden('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.16/1.32  tff(c_197, plain, (![A_79, C_80, B_81, D_82]: (r2_hidden(A_79, k9_relat_1(C_80, B_81)) | ~r2_hidden(D_82, B_81) | ~r2_hidden(k4_tarski(D_82, A_79), C_80) | ~r2_hidden(D_82, k1_relat_1(C_80)) | ~v1_relat_1(C_80))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.16/1.32  tff(c_228, plain, (![A_83, C_84]: (r2_hidden(A_83, k9_relat_1(C_84, '#skF_4')) | ~r2_hidden(k4_tarski('#skF_7', A_83), C_84) | ~r2_hidden('#skF_7', k1_relat_1(C_84)) | ~v1_relat_1(C_84))), inference(resolution, [status(thm)], [c_40, c_197])).
% 2.16/1.32  tff(c_235, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_129, c_228])).
% 2.16/1.32  tff(c_247, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_42, c_167, c_235])).
% 2.16/1.32  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_247])).
% 2.16/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.32  
% 2.16/1.32  Inference rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Ref     : 0
% 2.16/1.32  #Sup     : 41
% 2.16/1.32  #Fact    : 0
% 2.16/1.32  #Define  : 0
% 2.16/1.32  #Split   : 2
% 2.16/1.32  #Chain   : 0
% 2.16/1.32  #Close   : 0
% 2.16/1.32  
% 2.16/1.32  Ordering : KBO
% 2.16/1.32  
% 2.16/1.32  Simplification rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Subsume      : 2
% 2.16/1.32  #Demod        : 48
% 2.16/1.32  #Tautology    : 16
% 2.16/1.32  #SimpNegUnit  : 4
% 2.16/1.32  #BackRed      : 11
% 2.16/1.32  
% 2.16/1.32  #Partial instantiations: 0
% 2.16/1.32  #Strategies tried      : 1
% 2.16/1.32  
% 2.16/1.32  Timing (in seconds)
% 2.16/1.32  ----------------------
% 2.16/1.33  Preprocessing        : 0.32
% 2.16/1.33  Parsing              : 0.16
% 2.16/1.33  CNF conversion       : 0.02
% 2.16/1.33  Main loop            : 0.21
% 2.16/1.33  Inferencing          : 0.08
% 2.16/1.33  Reduction            : 0.07
% 2.16/1.33  Demodulation         : 0.05
% 2.16/1.33  BG Simplification    : 0.02
% 2.16/1.33  Subsumption          : 0.04
% 2.16/1.33  Abstraction          : 0.01
% 2.16/1.33  MUC search           : 0.00
% 2.16/1.33  Cooper               : 0.00
% 2.16/1.33  Total                : 0.56
% 2.16/1.33  Index Insertion      : 0.00
% 2.16/1.33  Index Deletion       : 0.00
% 2.16/1.33  Index Matching       : 0.00
% 2.16/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
