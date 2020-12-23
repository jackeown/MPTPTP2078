%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:57 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 125 expanded)
%              Number of leaves         :   38 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 270 expanded)
%              Number of equality atoms :   30 (  96 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | r1_tarski(C,k8_relset_1(A,B,D,k7_relset_1(A,B,D,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_40,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_44,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_53,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_154,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_158,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_154])).

tff(c_346,plain,(
    ! [B_115,A_116,C_117] :
      ( k1_xboole_0 = B_115
      | k1_relset_1(A_116,B_115,C_117) = A_116
      | ~ v1_funct_2(C_117,A_116,B_115)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_349,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_346])).

tff(c_352,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_158,c_349])).

tff(c_353,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_352])).

tff(c_18,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_61,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_64,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_61])).

tff(c_67,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_64])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,k10_relat_1(B_19,k9_relat_1(B_19,A_18)))
      | ~ r1_tarski(A_18,k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_236,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( k7_relset_1(A_84,B_85,C_86,D_87) = k9_relat_1(C_86,D_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_239,plain,(
    ! [D_87] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_87) = k9_relat_1('#skF_6',D_87) ),
    inference(resolution,[status(thm)],[c_46,c_236])).

tff(c_218,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k8_relset_1(A_79,B_80,C_81,D_82) = k10_relat_1(C_81,D_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_221,plain,(
    ! [D_82] : k8_relset_1('#skF_3','#skF_4','#skF_6',D_82) = k10_relat_1('#skF_6',D_82) ),
    inference(resolution,[status(thm)],[c_46,c_218])).

tff(c_40,plain,(
    ~ r1_tarski('#skF_5',k8_relset_1('#skF_3','#skF_4','#skF_6',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_222,plain,(
    ~ r1_tarski('#skF_5',k10_relat_1('#skF_6',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_40])).

tff(c_240,plain,(
    ~ r1_tarski('#skF_5',k10_relat_1('#skF_6',k9_relat_1('#skF_6','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_222])).

tff(c_252,plain,
    ( ~ r1_tarski('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_240])).

tff(c_258,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_252])).

tff(c_354,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_258])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_354])).

tff(c_360,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_359,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_366,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_359])).

tff(c_373,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_44])).

tff(c_12,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_361,plain,(
    ! [A_10] : r1_xboole_0(A_10,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_12])).

tff(c_378,plain,(
    ! [A_10] : r1_xboole_0(A_10,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_361])).

tff(c_394,plain,(
    ! [B_124,A_125] :
      ( ~ r1_xboole_0(B_124,A_125)
      | ~ r1_tarski(B_124,A_125)
      | v1_xboole_0(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_399,plain,(
    ! [A_126] :
      ( ~ r1_tarski(A_126,'#skF_4')
      | v1_xboole_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_378,c_394])).

tff(c_403,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_373,c_399])).

tff(c_405,plain,(
    ! [A_129,B_130] :
      ( r2_hidden('#skF_2'(A_129,B_130),A_129)
      | r1_tarski(A_129,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_428,plain,(
    ! [A_135,B_136] :
      ( ~ v1_xboole_0(A_135)
      | r1_tarski(A_135,B_136) ) ),
    inference(resolution,[status(thm)],[c_405,c_2])).

tff(c_393,plain,(
    ~ r1_tarski('#skF_5',k8_relset_1('#skF_4','#skF_4','#skF_6',k7_relset_1('#skF_4','#skF_4','#skF_6','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_366,c_40])).

tff(c_435,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_428,c_393])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:45:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.46  
% 2.97/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.46  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 2.97/1.46  
% 2.97/1.46  %Foreground sorts:
% 2.97/1.46  
% 2.97/1.46  
% 2.97/1.46  %Background operators:
% 2.97/1.46  
% 2.97/1.46  
% 2.97/1.46  %Foreground operators:
% 2.97/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.97/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.46  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.97/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.97/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.46  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.97/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.97/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.97/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.97/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.97/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.97/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.97/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.97/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.97/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.97/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.97/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.97/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.46  
% 2.97/1.48  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r1_tarski(C, k8_relset_1(A, B, D, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_2)).
% 2.97/1.48  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.97/1.48  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.97/1.48  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.97/1.48  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.97/1.48  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 2.97/1.48  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.97/1.48  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.97/1.48  tff(f_40, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.97/1.48  tff(f_48, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.97/1.48  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.97/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.97/1.48  tff(c_44, plain, (r1_tarski('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.97/1.48  tff(c_42, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.97/1.48  tff(c_53, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_42])).
% 2.97/1.48  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.97/1.48  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.97/1.48  tff(c_154, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.97/1.48  tff(c_158, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_154])).
% 2.97/1.48  tff(c_346, plain, (![B_115, A_116, C_117]: (k1_xboole_0=B_115 | k1_relset_1(A_116, B_115, C_117)=A_116 | ~v1_funct_2(C_117, A_116, B_115) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.97/1.48  tff(c_349, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_346])).
% 2.97/1.48  tff(c_352, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_158, c_349])).
% 2.97/1.48  tff(c_353, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_53, c_352])).
% 2.97/1.48  tff(c_18, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.97/1.48  tff(c_61, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.97/1.48  tff(c_64, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_61])).
% 2.97/1.48  tff(c_67, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_64])).
% 2.97/1.48  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(A_18, k10_relat_1(B_19, k9_relat_1(B_19, A_18))) | ~r1_tarski(A_18, k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.97/1.48  tff(c_236, plain, (![A_84, B_85, C_86, D_87]: (k7_relset_1(A_84, B_85, C_86, D_87)=k9_relat_1(C_86, D_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.97/1.48  tff(c_239, plain, (![D_87]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_87)=k9_relat_1('#skF_6', D_87))), inference(resolution, [status(thm)], [c_46, c_236])).
% 2.97/1.48  tff(c_218, plain, (![A_79, B_80, C_81, D_82]: (k8_relset_1(A_79, B_80, C_81, D_82)=k10_relat_1(C_81, D_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.97/1.48  tff(c_221, plain, (![D_82]: (k8_relset_1('#skF_3', '#skF_4', '#skF_6', D_82)=k10_relat_1('#skF_6', D_82))), inference(resolution, [status(thm)], [c_46, c_218])).
% 2.97/1.48  tff(c_40, plain, (~r1_tarski('#skF_5', k8_relset_1('#skF_3', '#skF_4', '#skF_6', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.97/1.48  tff(c_222, plain, (~r1_tarski('#skF_5', k10_relat_1('#skF_6', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_40])).
% 2.97/1.48  tff(c_240, plain, (~r1_tarski('#skF_5', k10_relat_1('#skF_6', k9_relat_1('#skF_6', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_222])).
% 2.97/1.48  tff(c_252, plain, (~r1_tarski('#skF_5', k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_240])).
% 2.97/1.48  tff(c_258, plain, (~r1_tarski('#skF_5', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_252])).
% 2.97/1.48  tff(c_354, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_353, c_258])).
% 2.97/1.48  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_354])).
% 2.97/1.48  tff(c_360, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_42])).
% 2.97/1.48  tff(c_359, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 2.97/1.48  tff(c_366, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_360, c_359])).
% 2.97/1.48  tff(c_373, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_366, c_44])).
% 2.97/1.48  tff(c_12, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.97/1.48  tff(c_361, plain, (![A_10]: (r1_xboole_0(A_10, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_12])).
% 2.97/1.48  tff(c_378, plain, (![A_10]: (r1_xboole_0(A_10, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_361])).
% 2.97/1.48  tff(c_394, plain, (![B_124, A_125]: (~r1_xboole_0(B_124, A_125) | ~r1_tarski(B_124, A_125) | v1_xboole_0(B_124))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.97/1.48  tff(c_399, plain, (![A_126]: (~r1_tarski(A_126, '#skF_4') | v1_xboole_0(A_126))), inference(resolution, [status(thm)], [c_378, c_394])).
% 2.97/1.48  tff(c_403, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_373, c_399])).
% 2.97/1.48  tff(c_405, plain, (![A_129, B_130]: (r2_hidden('#skF_2'(A_129, B_130), A_129) | r1_tarski(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.97/1.48  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.48  tff(c_428, plain, (![A_135, B_136]: (~v1_xboole_0(A_135) | r1_tarski(A_135, B_136))), inference(resolution, [status(thm)], [c_405, c_2])).
% 2.97/1.48  tff(c_393, plain, (~r1_tarski('#skF_5', k8_relset_1('#skF_4', '#skF_4', '#skF_6', k7_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_366, c_40])).
% 2.97/1.48  tff(c_435, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_428, c_393])).
% 2.97/1.48  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_403, c_435])).
% 2.97/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.48  
% 2.97/1.48  Inference rules
% 2.97/1.48  ----------------------
% 2.97/1.48  #Ref     : 0
% 2.97/1.48  #Sup     : 84
% 2.97/1.48  #Fact    : 0
% 2.97/1.48  #Define  : 0
% 2.97/1.48  #Split   : 2
% 2.97/1.48  #Chain   : 0
% 2.97/1.48  #Close   : 0
% 2.97/1.48  
% 2.97/1.48  Ordering : KBO
% 2.97/1.48  
% 2.97/1.48  Simplification rules
% 2.97/1.48  ----------------------
% 2.97/1.48  #Subsume      : 21
% 2.97/1.48  #Demod        : 20
% 2.97/1.48  #Tautology    : 20
% 2.97/1.48  #SimpNegUnit  : 2
% 2.97/1.48  #BackRed      : 9
% 2.97/1.48  
% 2.97/1.48  #Partial instantiations: 0
% 2.97/1.48  #Strategies tried      : 1
% 2.97/1.48  
% 2.97/1.48  Timing (in seconds)
% 2.97/1.48  ----------------------
% 2.97/1.48  Preprocessing        : 0.35
% 2.97/1.48  Parsing              : 0.18
% 2.97/1.48  CNF conversion       : 0.02
% 2.97/1.48  Main loop            : 0.31
% 2.97/1.48  Inferencing          : 0.12
% 2.97/1.48  Reduction            : 0.08
% 2.97/1.48  Demodulation         : 0.06
% 2.97/1.48  BG Simplification    : 0.02
% 2.97/1.48  Subsumption          : 0.07
% 2.97/1.48  Abstraction          : 0.01
% 2.97/1.48  MUC search           : 0.00
% 2.97/1.48  Cooper               : 0.00
% 2.97/1.48  Total                : 0.69
% 2.97/1.48  Index Insertion      : 0.00
% 2.97/1.48  Index Deletion       : 0.00
% 2.97/1.48  Index Matching       : 0.00
% 2.97/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
