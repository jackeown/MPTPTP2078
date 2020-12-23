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
% DateTime   : Thu Dec  3 10:15:13 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 106 expanded)
%              Number of leaves         :   46 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 186 expanded)
%              Number of equality atoms :   33 (  61 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_150,plain,(
    ! [A_111,B_112] :
      ( ~ r2_hidden(A_111,B_112)
      | k4_xboole_0(k1_tarski(A_111),B_112) != k1_tarski(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_159,plain,(
    ! [A_111] : ~ r2_hidden(A_111,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_150])).

tff(c_74,plain,(
    k1_funct_1('#skF_10','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_76,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_78,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_117,plain,(
    ! [C_103,A_104,B_105] :
      ( v1_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_121,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_117])).

tff(c_82,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_80,plain,(
    v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_191,plain,(
    ! [A_132,B_133,C_134] :
      ( k1_relset_1(A_132,B_133,C_134) = k1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_195,plain,(
    k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_191])).

tff(c_425,plain,(
    ! [B_183,A_184,C_185] :
      ( k1_xboole_0 = B_183
      | k1_relset_1(A_184,B_183,C_185) = A_184
      | ~ v1_funct_2(C_185,A_184,B_183)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_184,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_432,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_78,c_425])).

tff(c_436,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_195,c_432])).

tff(c_437,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_436])).

tff(c_180,plain,(
    ! [A_126,B_127,C_128] :
      ( k2_relset_1(A_126,B_127,C_128) = k2_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_184,plain,(
    k2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_180])).

tff(c_288,plain,(
    ! [A_141,B_142,C_143] :
      ( m1_subset_1(k2_relset_1(A_141,B_142,C_143),k1_zfmisc_1(B_142))
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_303,plain,
    ( m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(k1_tarski('#skF_8')))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_288])).

tff(c_308,plain,(
    m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_303])).

tff(c_324,plain,(
    ! [A_151,D_152] :
      ( r2_hidden(k1_funct_1(A_151,D_152),k2_relat_1(A_151))
      | ~ r2_hidden(D_152,k1_relat_1(A_151))
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,(
    ! [C_40,A_37,B_38] :
      ( r2_hidden(C_40,A_37)
      | ~ r2_hidden(C_40,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_791,plain,(
    ! [A_235,D_236,A_237] :
      ( r2_hidden(k1_funct_1(A_235,D_236),A_237)
      | ~ m1_subset_1(k2_relat_1(A_235),k1_zfmisc_1(A_237))
      | ~ r2_hidden(D_236,k1_relat_1(A_235))
      | ~ v1_funct_1(A_235)
      | ~ v1_relat_1(A_235) ) ),
    inference(resolution,[status(thm)],[c_324,c_34])).

tff(c_793,plain,(
    ! [D_236] :
      ( r2_hidden(k1_funct_1('#skF_10',D_236),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_236,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_308,c_791])).

tff(c_797,plain,(
    ! [D_238] :
      ( r2_hidden(k1_funct_1('#skF_10',D_238),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_238,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_82,c_437,c_793])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_844,plain,(
    ! [D_239] :
      ( k1_funct_1('#skF_10',D_239) = '#skF_8'
      | ~ r2_hidden(D_239,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_797,c_4])).

tff(c_897,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_76,c_844])).

tff(c_914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_897])).

tff(c_915,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_959,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_6])).

tff(c_968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_959])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:23:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.57  
% 3.35/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.57  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 3.35/1.57  
% 3.35/1.57  %Foreground sorts:
% 3.35/1.57  
% 3.35/1.57  
% 3.35/1.57  %Background operators:
% 3.35/1.57  
% 3.35/1.57  
% 3.35/1.57  %Foreground operators:
% 3.35/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.35/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.35/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.35/1.57  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.35/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.35/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.35/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.35/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.35/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.35/1.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.35/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.35/1.57  tff('#skF_10', type, '#skF_10': $i).
% 3.35/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.35/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.35/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.35/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.35/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.57  tff('#skF_9', type, '#skF_9': $i).
% 3.35/1.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.35/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.35/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.35/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.35/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.35/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.35/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.35/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.35/1.57  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.35/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.35/1.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.35/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.57  
% 3.60/1.58  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.60/1.58  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 3.60/1.58  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.60/1.58  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.60/1.58  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.60/1.58  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.60/1.58  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.60/1.58  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.60/1.58  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.60/1.58  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.60/1.58  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.60/1.58  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.60/1.58  tff(c_150, plain, (![A_111, B_112]: (~r2_hidden(A_111, B_112) | k4_xboole_0(k1_tarski(A_111), B_112)!=k1_tarski(A_111))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.60/1.58  tff(c_159, plain, (![A_111]: (~r2_hidden(A_111, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_150])).
% 3.60/1.58  tff(c_74, plain, (k1_funct_1('#skF_10', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.60/1.58  tff(c_76, plain, (r2_hidden('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.60/1.58  tff(c_78, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.60/1.58  tff(c_117, plain, (![C_103, A_104, B_105]: (v1_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.60/1.58  tff(c_121, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_78, c_117])).
% 3.60/1.58  tff(c_82, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.60/1.58  tff(c_80, plain, (v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.60/1.58  tff(c_191, plain, (![A_132, B_133, C_134]: (k1_relset_1(A_132, B_133, C_134)=k1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.60/1.58  tff(c_195, plain, (k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_78, c_191])).
% 3.60/1.58  tff(c_425, plain, (![B_183, A_184, C_185]: (k1_xboole_0=B_183 | k1_relset_1(A_184, B_183, C_185)=A_184 | ~v1_funct_2(C_185, A_184, B_183) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_184, B_183))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.60/1.58  tff(c_432, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_78, c_425])).
% 3.60/1.58  tff(c_436, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_195, c_432])).
% 3.60/1.58  tff(c_437, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_436])).
% 3.60/1.58  tff(c_180, plain, (![A_126, B_127, C_128]: (k2_relset_1(A_126, B_127, C_128)=k2_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.60/1.58  tff(c_184, plain, (k2_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_78, c_180])).
% 3.60/1.58  tff(c_288, plain, (![A_141, B_142, C_143]: (m1_subset_1(k2_relset_1(A_141, B_142, C_143), k1_zfmisc_1(B_142)) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.60/1.58  tff(c_303, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(k1_tarski('#skF_8'))) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(superposition, [status(thm), theory('equality')], [c_184, c_288])).
% 3.60/1.58  tff(c_308, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_303])).
% 3.60/1.58  tff(c_324, plain, (![A_151, D_152]: (r2_hidden(k1_funct_1(A_151, D_152), k2_relat_1(A_151)) | ~r2_hidden(D_152, k1_relat_1(A_151)) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.60/1.58  tff(c_34, plain, (![C_40, A_37, B_38]: (r2_hidden(C_40, A_37) | ~r2_hidden(C_40, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.60/1.58  tff(c_791, plain, (![A_235, D_236, A_237]: (r2_hidden(k1_funct_1(A_235, D_236), A_237) | ~m1_subset_1(k2_relat_1(A_235), k1_zfmisc_1(A_237)) | ~r2_hidden(D_236, k1_relat_1(A_235)) | ~v1_funct_1(A_235) | ~v1_relat_1(A_235))), inference(resolution, [status(thm)], [c_324, c_34])).
% 3.60/1.58  tff(c_793, plain, (![D_236]: (r2_hidden(k1_funct_1('#skF_10', D_236), k1_tarski('#skF_8')) | ~r2_hidden(D_236, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_308, c_791])).
% 3.60/1.58  tff(c_797, plain, (![D_238]: (r2_hidden(k1_funct_1('#skF_10', D_238), k1_tarski('#skF_8')) | ~r2_hidden(D_238, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_82, c_437, c_793])).
% 3.60/1.58  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.60/1.58  tff(c_844, plain, (![D_239]: (k1_funct_1('#skF_10', D_239)='#skF_8' | ~r2_hidden(D_239, '#skF_7'))), inference(resolution, [status(thm)], [c_797, c_4])).
% 3.60/1.58  tff(c_897, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_76, c_844])).
% 3.60/1.58  tff(c_914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_897])).
% 3.60/1.58  tff(c_915, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_436])).
% 3.60/1.58  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.60/1.58  tff(c_959, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_915, c_6])).
% 3.60/1.58  tff(c_968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_959])).
% 3.60/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.58  
% 3.60/1.58  Inference rules
% 3.60/1.58  ----------------------
% 3.60/1.58  #Ref     : 0
% 3.60/1.58  #Sup     : 187
% 3.60/1.58  #Fact    : 2
% 3.60/1.58  #Define  : 0
% 3.60/1.58  #Split   : 7
% 3.60/1.58  #Chain   : 0
% 3.60/1.58  #Close   : 0
% 3.60/1.58  
% 3.60/1.58  Ordering : KBO
% 3.60/1.58  
% 3.60/1.58  Simplification rules
% 3.60/1.58  ----------------------
% 3.60/1.58  #Subsume      : 20
% 3.60/1.58  #Demod        : 84
% 3.60/1.58  #Tautology    : 76
% 3.60/1.58  #SimpNegUnit  : 10
% 3.60/1.58  #BackRed      : 16
% 3.60/1.58  
% 3.60/1.58  #Partial instantiations: 0
% 3.60/1.58  #Strategies tried      : 1
% 3.60/1.58  
% 3.60/1.58  Timing (in seconds)
% 3.60/1.58  ----------------------
% 3.60/1.58  Preprocessing        : 0.37
% 3.60/1.58  Parsing              : 0.19
% 3.60/1.58  CNF conversion       : 0.03
% 3.60/1.58  Main loop            : 0.42
% 3.60/1.58  Inferencing          : 0.16
% 3.60/1.58  Reduction            : 0.12
% 3.60/1.59  Demodulation         : 0.07
% 3.60/1.59  BG Simplification    : 0.03
% 3.60/1.59  Subsumption          : 0.08
% 3.60/1.59  Abstraction          : 0.03
% 3.60/1.59  MUC search           : 0.00
% 3.60/1.59  Cooper               : 0.00
% 3.60/1.59  Total                : 0.82
% 3.60/1.59  Index Insertion      : 0.00
% 3.60/1.59  Index Deletion       : 0.00
% 3.60/1.59  Index Matching       : 0.00
% 3.60/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
