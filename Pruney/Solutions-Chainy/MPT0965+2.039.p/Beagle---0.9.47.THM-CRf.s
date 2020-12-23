%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:05 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   80 (  98 expanded)
%              Number of leaves         :   40 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  119 ( 192 expanded)
%              Number of equality atoms :   32 (  43 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k6_subset_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_113,axiom,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_95,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_100,plain,(
    ! [C_64,B_65,A_66] :
      ( v5_relat_1(C_64,B_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_109,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_100])).

tff(c_50,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_18,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_82,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_88,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_82])).

tff(c_92,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_88])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_169,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_178,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_169])).

tff(c_238,plain,(
    ! [B_137,A_138,C_139] :
      ( k1_xboole_0 = B_137
      | k1_relset_1(A_138,B_137,C_139) = A_138
      | ~ v1_funct_2(C_139,A_138,B_137)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_245,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_238])).

tff(c_250,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_178,c_245])).

tff(c_251,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_250])).

tff(c_20,plain,(
    ! [C_21,B_20,A_19] :
      ( m1_subset_1(k1_funct_1(C_21,B_20),A_19)
      | ~ r2_hidden(B_20,k1_relat_1(C_21))
      | ~ v1_funct_1(C_21)
      | ~ v5_relat_1(C_21,A_19)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_255,plain,(
    ! [B_20,A_19] :
      ( m1_subset_1(k1_funct_1('#skF_5',B_20),A_19)
      | ~ r2_hidden(B_20,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_19)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_20])).

tff(c_278,plain,(
    ! [B_143,A_144] :
      ( m1_subset_1(k1_funct_1('#skF_5',B_143),A_144)
      | ~ r2_hidden(B_143,'#skF_2')
      | ~ v5_relat_1('#skF_5',A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_56,c_255])).

tff(c_93,plain,(
    ! [A_60,B_61] :
      ( r2_hidden(A_60,B_61)
      | v1_xboole_0(B_61)
      | ~ m1_subset_1(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_97,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_46])).

tff(c_99,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_320,plain,
    ( ~ r2_hidden('#skF_4','#skF_2')
    | ~ v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_278,c_99])).

tff(c_338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_50,c_320])).

tff(c_339,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_28,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28),A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_10,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_5,B_6] : m1_subset_1(k6_subset_1(A_5,B_6),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_5,B_6] : m1_subset_1(k4_xboole_0(A_5,B_6),k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8])).

tff(c_353,plain,(
    ! [C_153,B_154,A_155] :
      ( ~ v1_xboole_0(C_153)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(C_153))
      | ~ r2_hidden(A_155,B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_370,plain,(
    ! [A_159,A_160,B_161] :
      ( ~ v1_xboole_0(A_159)
      | ~ r2_hidden(A_160,k4_xboole_0(A_159,B_161)) ) ),
    inference(resolution,[status(thm)],[c_57,c_353])).

tff(c_381,plain,(
    ! [A_162,B_163] :
      ( ~ v1_xboole_0(A_162)
      | k4_xboole_0(A_162,B_163) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_370])).

tff(c_386,plain,(
    ! [B_164] : k4_xboole_0('#skF_3',B_164) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_339,c_381])).

tff(c_71,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | k4_xboole_0(A_54,B_55) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    ! [A_54,B_4] :
      ( k1_xboole_0 = A_54
      | k4_xboole_0(A_54,k4_xboole_0(B_4,A_54)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_71,c_6])).

tff(c_398,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_76])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:15:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.31  
% 2.55/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.31  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k6_subset_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.55/1.31  
% 2.55/1.31  %Foreground sorts:
% 2.55/1.31  
% 2.55/1.31  
% 2.55/1.31  %Background operators:
% 2.55/1.31  
% 2.55/1.31  
% 2.55/1.31  %Foreground operators:
% 2.55/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.55/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.55/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.55/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.31  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.55/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.55/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.55/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.31  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.55/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.55/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.55/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.55/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.55/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.55/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.55/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.55/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.31  
% 2.55/1.33  tff(f_126, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.55/1.33  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.55/1.33  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.55/1.33  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.55/1.33  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.55/1.33  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.55/1.33  tff(f_69, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 2.55/1.33  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.55/1.33  tff(f_95, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 2.55/1.33  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.55/1.33  tff(f_35, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.55/1.33  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.55/1.33  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.55/1.33  tff(f_33, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.55/1.33  tff(c_48, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.55/1.33  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.55/1.33  tff(c_100, plain, (![C_64, B_65, A_66]: (v5_relat_1(C_64, B_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.55/1.33  tff(c_109, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_100])).
% 2.55/1.33  tff(c_50, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.55/1.33  tff(c_18, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.55/1.33  tff(c_82, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.55/1.33  tff(c_88, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_82])).
% 2.55/1.33  tff(c_92, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_88])).
% 2.55/1.33  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.55/1.33  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.55/1.33  tff(c_169, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.55/1.33  tff(c_178, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_169])).
% 2.55/1.33  tff(c_238, plain, (![B_137, A_138, C_139]: (k1_xboole_0=B_137 | k1_relset_1(A_138, B_137, C_139)=A_138 | ~v1_funct_2(C_139, A_138, B_137) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.55/1.33  tff(c_245, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_238])).
% 2.55/1.33  tff(c_250, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_178, c_245])).
% 2.55/1.33  tff(c_251, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_250])).
% 2.55/1.33  tff(c_20, plain, (![C_21, B_20, A_19]: (m1_subset_1(k1_funct_1(C_21, B_20), A_19) | ~r2_hidden(B_20, k1_relat_1(C_21)) | ~v1_funct_1(C_21) | ~v5_relat_1(C_21, A_19) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.55/1.33  tff(c_255, plain, (![B_20, A_19]: (m1_subset_1(k1_funct_1('#skF_5', B_20), A_19) | ~r2_hidden(B_20, '#skF_2') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_19) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_251, c_20])).
% 2.55/1.33  tff(c_278, plain, (![B_143, A_144]: (m1_subset_1(k1_funct_1('#skF_5', B_143), A_144) | ~r2_hidden(B_143, '#skF_2') | ~v5_relat_1('#skF_5', A_144))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_56, c_255])).
% 2.55/1.33  tff(c_93, plain, (![A_60, B_61]: (r2_hidden(A_60, B_61) | v1_xboole_0(B_61) | ~m1_subset_1(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.55/1.33  tff(c_46, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.55/1.33  tff(c_97, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_93, c_46])).
% 2.55/1.33  tff(c_99, plain, (~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_97])).
% 2.55/1.33  tff(c_320, plain, (~r2_hidden('#skF_4', '#skF_2') | ~v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_278, c_99])).
% 2.55/1.33  tff(c_338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_50, c_320])).
% 2.55/1.33  tff(c_339, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_97])).
% 2.55/1.33  tff(c_28, plain, (![A_28]: (r2_hidden('#skF_1'(A_28), A_28) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.55/1.33  tff(c_10, plain, (![A_7, B_8]: (k6_subset_1(A_7, B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.55/1.33  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k6_subset_1(A_5, B_6), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.55/1.33  tff(c_57, plain, (![A_5, B_6]: (m1_subset_1(k4_xboole_0(A_5, B_6), k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8])).
% 2.55/1.33  tff(c_353, plain, (![C_153, B_154, A_155]: (~v1_xboole_0(C_153) | ~m1_subset_1(B_154, k1_zfmisc_1(C_153)) | ~r2_hidden(A_155, B_154))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.55/1.33  tff(c_370, plain, (![A_159, A_160, B_161]: (~v1_xboole_0(A_159) | ~r2_hidden(A_160, k4_xboole_0(A_159, B_161)))), inference(resolution, [status(thm)], [c_57, c_353])).
% 2.55/1.33  tff(c_381, plain, (![A_162, B_163]: (~v1_xboole_0(A_162) | k4_xboole_0(A_162, B_163)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_370])).
% 2.55/1.33  tff(c_386, plain, (![B_164]: (k4_xboole_0('#skF_3', B_164)=k1_xboole_0)), inference(resolution, [status(thm)], [c_339, c_381])).
% 2.55/1.33  tff(c_71, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | k4_xboole_0(A_54, B_55)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.33  tff(c_6, plain, (![A_3, B_4]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k4_xboole_0(B_4, A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.55/1.33  tff(c_76, plain, (![A_54, B_4]: (k1_xboole_0=A_54 | k4_xboole_0(A_54, k4_xboole_0(B_4, A_54))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_71, c_6])).
% 2.55/1.33  tff(c_398, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_386, c_76])).
% 2.55/1.33  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_398])).
% 2.55/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.33  
% 2.55/1.33  Inference rules
% 2.55/1.33  ----------------------
% 2.55/1.33  #Ref     : 0
% 2.55/1.33  #Sup     : 72
% 2.55/1.33  #Fact    : 0
% 2.55/1.33  #Define  : 0
% 2.55/1.33  #Split   : 5
% 2.55/1.33  #Chain   : 0
% 2.55/1.33  #Close   : 0
% 2.55/1.33  
% 2.55/1.33  Ordering : KBO
% 2.55/1.33  
% 2.55/1.33  Simplification rules
% 2.55/1.33  ----------------------
% 2.55/1.33  #Subsume      : 0
% 2.55/1.33  #Demod        : 15
% 2.55/1.33  #Tautology    : 15
% 2.55/1.33  #SimpNegUnit  : 3
% 2.55/1.33  #BackRed      : 1
% 2.55/1.33  
% 2.55/1.33  #Partial instantiations: 0
% 2.55/1.33  #Strategies tried      : 1
% 2.55/1.33  
% 2.55/1.33  Timing (in seconds)
% 2.55/1.33  ----------------------
% 2.55/1.33  Preprocessing        : 0.32
% 2.55/1.33  Parsing              : 0.17
% 2.55/1.33  CNF conversion       : 0.02
% 2.55/1.33  Main loop            : 0.25
% 2.55/1.33  Inferencing          : 0.09
% 2.55/1.33  Reduction            : 0.07
% 2.55/1.33  Demodulation         : 0.05
% 2.55/1.33  BG Simplification    : 0.02
% 2.55/1.33  Subsumption          : 0.04
% 2.55/1.33  Abstraction          : 0.01
% 2.55/1.33  MUC search           : 0.00
% 2.55/1.33  Cooper               : 0.00
% 2.55/1.33  Total                : 0.60
% 2.55/1.33  Index Insertion      : 0.00
% 2.55/1.33  Index Deletion       : 0.00
% 2.55/1.33  Index Matching       : 0.00
% 2.55/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
