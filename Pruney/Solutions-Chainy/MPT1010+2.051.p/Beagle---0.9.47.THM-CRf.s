%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:12 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 106 expanded)
%              Number of leaves         :   41 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 195 expanded)
%              Number of equality atoms :   33 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_78,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_80,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_82,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_181,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_185,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_82,c_181])).

tff(c_86,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_84,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_288,plain,(
    ! [A_121,B_122,C_123] :
      ( k1_relset_1(A_121,B_122,C_123) = k1_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_292,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_82,c_288])).

tff(c_388,plain,(
    ! [B_156,A_157,C_158] :
      ( k1_xboole_0 = B_156
      | k1_relset_1(A_157,B_156,C_158) = A_157
      | ~ v1_funct_2(C_158,A_157,B_156)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_157,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_395,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_82,c_388])).

tff(c_399,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_292,c_395])).

tff(c_401,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_399])).

tff(c_256,plain,(
    ! [A_110,B_111,C_112] :
      ( k2_relset_1(A_110,B_111,C_112) = k2_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_260,plain,(
    k2_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_82,c_256])).

tff(c_297,plain,(
    ! [A_124,B_125,C_126] :
      ( m1_subset_1(k2_relset_1(A_124,B_125,C_126),k1_zfmisc_1(B_125))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_312,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1(k1_tarski('#skF_6')))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_297])).

tff(c_317,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1(k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_312])).

tff(c_324,plain,(
    ! [B_129,A_130] :
      ( r2_hidden(k1_funct_1(B_129,A_130),k2_relat_1(B_129))
      | ~ r2_hidden(A_130,k1_relat_1(B_129))
      | ~ v1_funct_1(B_129)
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    ! [C_24,A_21,B_22] :
      ( r2_hidden(C_24,A_21)
      | ~ r2_hidden(C_24,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_413,plain,(
    ! [B_171,A_172,A_173] :
      ( r2_hidden(k1_funct_1(B_171,A_172),A_173)
      | ~ m1_subset_1(k2_relat_1(B_171),k1_zfmisc_1(A_173))
      | ~ r2_hidden(A_172,k1_relat_1(B_171))
      | ~ v1_funct_1(B_171)
      | ~ v1_relat_1(B_171) ) ),
    inference(resolution,[status(thm)],[c_324,c_52])).

tff(c_415,plain,(
    ! [A_172] :
      ( r2_hidden(k1_funct_1('#skF_8',A_172),k1_tarski('#skF_6'))
      | ~ r2_hidden(A_172,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_317,c_413])).

tff(c_419,plain,(
    ! [A_174] :
      ( r2_hidden(k1_funct_1('#skF_8',A_174),k1_tarski('#skF_6'))
      | ~ r2_hidden(A_174,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_86,c_401,c_415])).

tff(c_46,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_195,plain,(
    ! [D_84,B_85,A_86] :
      ( D_84 = B_85
      | D_84 = A_86
      | ~ r2_hidden(D_84,k2_tarski(A_86,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_204,plain,(
    ! [D_84,A_15] :
      ( D_84 = A_15
      | D_84 = A_15
      | ~ r2_hidden(D_84,k1_tarski(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_195])).

tff(c_431,plain,(
    ! [A_175] :
      ( k1_funct_1('#skF_8',A_175) = '#skF_6'
      | ~ r2_hidden(A_175,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_419,c_204])).

tff(c_438,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_80,c_431])).

tff(c_443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_438])).

tff(c_444,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_399])).

tff(c_97,plain,(
    ! [D_46,A_47] : r2_hidden(D_46,k2_tarski(A_47,D_46)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_100,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_97])).

tff(c_109,plain,(
    ! [B_57,A_58] :
      ( ~ r1_tarski(B_57,A_58)
      | ~ r2_hidden(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_131,plain,(
    ! [A_15] : ~ r1_tarski(k1_tarski(A_15),A_15) ),
    inference(resolution,[status(thm)],[c_100,c_109])).

tff(c_460,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_131])).

tff(c_468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:22:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.37  
% 2.80/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.38  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 2.80/1.38  
% 2.80/1.38  %Foreground sorts:
% 2.80/1.38  
% 2.80/1.38  
% 2.80/1.38  %Background operators:
% 2.80/1.38  
% 2.80/1.38  
% 2.80/1.38  %Foreground operators:
% 2.80/1.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.80/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.80/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.80/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.80/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.80/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.80/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.80/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.80/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.80/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.80/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.80/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.80/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.80/1.38  tff('#skF_8', type, '#skF_8': $i).
% 2.80/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.80/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.80/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.80/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.80/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.80/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.38  
% 2.80/1.39  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.80/1.39  tff(f_122, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.80/1.39  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.80/1.39  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.80/1.39  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.80/1.39  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.80/1.39  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.80/1.39  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.80/1.39  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.80/1.39  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.80/1.39  tff(f_51, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.80/1.39  tff(f_77, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.80/1.39  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.80/1.39  tff(c_78, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.80/1.39  tff(c_80, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.80/1.39  tff(c_82, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.80/1.39  tff(c_181, plain, (![C_78, A_79, B_80]: (v1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.80/1.39  tff(c_185, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_82, c_181])).
% 2.80/1.39  tff(c_86, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.80/1.39  tff(c_84, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.80/1.39  tff(c_288, plain, (![A_121, B_122, C_123]: (k1_relset_1(A_121, B_122, C_123)=k1_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.80/1.39  tff(c_292, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_82, c_288])).
% 2.80/1.39  tff(c_388, plain, (![B_156, A_157, C_158]: (k1_xboole_0=B_156 | k1_relset_1(A_157, B_156, C_158)=A_157 | ~v1_funct_2(C_158, A_157, B_156) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.80/1.39  tff(c_395, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_82, c_388])).
% 2.80/1.39  tff(c_399, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_292, c_395])).
% 2.80/1.39  tff(c_401, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_399])).
% 2.80/1.39  tff(c_256, plain, (![A_110, B_111, C_112]: (k2_relset_1(A_110, B_111, C_112)=k2_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.80/1.39  tff(c_260, plain, (k2_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_82, c_256])).
% 2.80/1.39  tff(c_297, plain, (![A_124, B_125, C_126]: (m1_subset_1(k2_relset_1(A_124, B_125, C_126), k1_zfmisc_1(B_125)) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.80/1.39  tff(c_312, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1(k1_tarski('#skF_6'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_260, c_297])).
% 2.80/1.39  tff(c_317, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1(k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_312])).
% 2.80/1.39  tff(c_324, plain, (![B_129, A_130]: (r2_hidden(k1_funct_1(B_129, A_130), k2_relat_1(B_129)) | ~r2_hidden(A_130, k1_relat_1(B_129)) | ~v1_funct_1(B_129) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.80/1.39  tff(c_52, plain, (![C_24, A_21, B_22]: (r2_hidden(C_24, A_21) | ~r2_hidden(C_24, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.80/1.39  tff(c_413, plain, (![B_171, A_172, A_173]: (r2_hidden(k1_funct_1(B_171, A_172), A_173) | ~m1_subset_1(k2_relat_1(B_171), k1_zfmisc_1(A_173)) | ~r2_hidden(A_172, k1_relat_1(B_171)) | ~v1_funct_1(B_171) | ~v1_relat_1(B_171))), inference(resolution, [status(thm)], [c_324, c_52])).
% 2.80/1.39  tff(c_415, plain, (![A_172]: (r2_hidden(k1_funct_1('#skF_8', A_172), k1_tarski('#skF_6')) | ~r2_hidden(A_172, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_317, c_413])).
% 2.80/1.39  tff(c_419, plain, (![A_174]: (r2_hidden(k1_funct_1('#skF_8', A_174), k1_tarski('#skF_6')) | ~r2_hidden(A_174, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_86, c_401, c_415])).
% 2.80/1.39  tff(c_46, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.80/1.39  tff(c_195, plain, (![D_84, B_85, A_86]: (D_84=B_85 | D_84=A_86 | ~r2_hidden(D_84, k2_tarski(A_86, B_85)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.80/1.39  tff(c_204, plain, (![D_84, A_15]: (D_84=A_15 | D_84=A_15 | ~r2_hidden(D_84, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_195])).
% 2.80/1.39  tff(c_431, plain, (![A_175]: (k1_funct_1('#skF_8', A_175)='#skF_6' | ~r2_hidden(A_175, '#skF_5'))), inference(resolution, [status(thm)], [c_419, c_204])).
% 2.80/1.39  tff(c_438, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_80, c_431])).
% 2.80/1.39  tff(c_443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_438])).
% 2.80/1.39  tff(c_444, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_399])).
% 2.80/1.39  tff(c_97, plain, (![D_46, A_47]: (r2_hidden(D_46, k2_tarski(A_47, D_46)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.80/1.39  tff(c_100, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_97])).
% 2.80/1.39  tff(c_109, plain, (![B_57, A_58]: (~r1_tarski(B_57, A_58) | ~r2_hidden(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.80/1.39  tff(c_131, plain, (![A_15]: (~r1_tarski(k1_tarski(A_15), A_15))), inference(resolution, [status(thm)], [c_100, c_109])).
% 2.80/1.39  tff(c_460, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_444, c_131])).
% 2.80/1.39  tff(c_468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_460])).
% 2.80/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.39  
% 2.80/1.39  Inference rules
% 2.80/1.39  ----------------------
% 2.80/1.39  #Ref     : 0
% 2.80/1.39  #Sup     : 85
% 2.80/1.39  #Fact    : 0
% 2.80/1.39  #Define  : 0
% 2.80/1.39  #Split   : 1
% 2.80/1.39  #Chain   : 0
% 2.80/1.39  #Close   : 0
% 2.80/1.39  
% 2.80/1.39  Ordering : KBO
% 2.80/1.39  
% 2.80/1.39  Simplification rules
% 2.80/1.39  ----------------------
% 2.80/1.39  #Subsume      : 11
% 2.80/1.39  #Demod        : 19
% 2.80/1.39  #Tautology    : 26
% 2.80/1.39  #SimpNegUnit  : 1
% 2.80/1.39  #BackRed      : 6
% 2.80/1.39  
% 2.80/1.39  #Partial instantiations: 0
% 2.80/1.39  #Strategies tried      : 1
% 2.80/1.39  
% 2.80/1.39  Timing (in seconds)
% 2.80/1.39  ----------------------
% 2.80/1.39  Preprocessing        : 0.35
% 2.80/1.39  Parsing              : 0.18
% 2.80/1.39  CNF conversion       : 0.03
% 2.80/1.39  Main loop            : 0.29
% 2.80/1.39  Inferencing          : 0.10
% 2.80/1.39  Reduction            : 0.09
% 2.80/1.39  Demodulation         : 0.06
% 2.80/1.39  BG Simplification    : 0.02
% 2.80/1.39  Subsumption          : 0.06
% 2.80/1.39  Abstraction          : 0.02
% 2.80/1.39  MUC search           : 0.00
% 2.80/1.39  Cooper               : 0.00
% 2.80/1.39  Total                : 0.67
% 2.80/1.39  Index Insertion      : 0.00
% 2.80/1.39  Index Deletion       : 0.00
% 2.80/1.39  Index Matching       : 0.00
% 2.80/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
