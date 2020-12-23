%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:28 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 140 expanded)
%              Number of leaves         :   34 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  120 ( 341 expanded)
%              Number of equality atoms :   38 ( 116 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_161,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_170,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_161])).

tff(c_50,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_171,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_50])).

tff(c_2018,plain,(
    ! [A_268,B_269,C_270] :
      ( r2_hidden('#skF_1'(A_268,B_269,C_270),B_269)
      | k2_relset_1(A_268,B_269,C_270) = B_269
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2033,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_2018])).

tff(c_2041,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_2033])).

tff(c_2042,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_2041])).

tff(c_60,plain,(
    ! [D_44] :
      ( r2_hidden('#skF_6'(D_44),'#skF_3')
      | ~ r2_hidden(D_44,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_136,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_145,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_136])).

tff(c_1747,plain,(
    ! [B_249,A_250,C_251] :
      ( k1_xboole_0 = B_249
      | k1_relset_1(A_250,B_249,C_251) = A_250
      | ~ v1_funct_2(C_251,A_250,B_249)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_250,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1765,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1747])).

tff(c_1773,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_145,c_1765])).

tff(c_1774,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1773])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_89,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_95,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_89])).

tff(c_99,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_95])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_58,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_5','#skF_6'(D_44)) = D_44
      | ~ r2_hidden(D_44,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1409,plain,(
    ! [A_213,C_214] :
      ( r2_hidden(k4_tarski(A_213,k1_funct_1(C_214,A_213)),C_214)
      | ~ r2_hidden(A_213,k1_relat_1(C_214))
      | ~ v1_funct_1(C_214)
      | ~ v1_relat_1(C_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1421,plain,(
    ! [D_44] :
      ( r2_hidden(k4_tarski('#skF_6'(D_44),D_44),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_44),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(D_44,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1409])).

tff(c_1427,plain,(
    ! [D_44] :
      ( r2_hidden(k4_tarski('#skF_6'(D_44),D_44),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_44),k1_relat_1('#skF_5'))
      | ~ r2_hidden(D_44,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_56,c_1421])).

tff(c_1776,plain,(
    ! [D_44] :
      ( r2_hidden(k4_tarski('#skF_6'(D_44),D_44),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_44),'#skF_3')
      | ~ r2_hidden(D_44,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1774,c_1427])).

tff(c_2133,plain,(
    ! [E_281,A_282,B_283,C_284] :
      ( ~ r2_hidden(k4_tarski(E_281,'#skF_1'(A_282,B_283,C_284)),C_284)
      | k2_relset_1(A_282,B_283,C_284) = B_283
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2139,plain,(
    ! [A_285,B_286] :
      ( k2_relset_1(A_285,B_286,'#skF_5') = B_286
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_285,B_286)))
      | ~ r2_hidden('#skF_6'('#skF_1'(A_285,B_286,'#skF_5')),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_285,B_286,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1776,c_2133])).

tff(c_2285,plain,(
    ! [A_309,B_310] :
      ( k2_relset_1(A_309,B_310,'#skF_5') = B_310
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_309,B_310)))
      | ~ r2_hidden('#skF_1'(A_309,B_310,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_2139])).

tff(c_2298,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_2285])).

tff(c_2306,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2042,c_170,c_2298])).

tff(c_2308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_2306])).

tff(c_2309,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1773])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2326,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2309,c_2])).

tff(c_2439,plain,(
    ! [A_319,B_320,C_321] :
      ( r2_hidden('#skF_1'(A_319,B_320,C_321),B_320)
      | k2_relset_1(A_319,B_320,C_321) = B_320
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(A_319,B_320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2452,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_2439])).

tff(c_2459,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_2452])).

tff(c_2460,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_2459])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2471,plain,(
    ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_2460,c_18])).

tff(c_2475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2326,c_2471])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.71  
% 4.15/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.71  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6
% 4.15/1.71  
% 4.15/1.71  %Foreground sorts:
% 4.15/1.71  
% 4.15/1.71  
% 4.15/1.71  %Background operators:
% 4.15/1.71  
% 4.15/1.71  
% 4.15/1.71  %Foreground operators:
% 4.15/1.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.15/1.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.15/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.15/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.15/1.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.15/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.15/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.15/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.15/1.71  tff('#skF_5', type, '#skF_5': $i).
% 4.15/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.15/1.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.15/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.15/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.15/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.15/1.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.15/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.15/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.15/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.15/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.15/1.71  tff('#skF_6', type, '#skF_6': $i > $i).
% 4.15/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.15/1.71  
% 4.15/1.73  tff(f_128, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 4.15/1.73  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.15/1.73  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 4.15/1.73  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.15/1.73  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.15/1.73  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.15/1.73  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.15/1.73  tff(f_50, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.15/1.73  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.15/1.73  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.15/1.73  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.15/1.73  tff(c_161, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.15/1.73  tff(c_170, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_161])).
% 4.15/1.73  tff(c_50, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.15/1.73  tff(c_171, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_50])).
% 4.15/1.73  tff(c_2018, plain, (![A_268, B_269, C_270]: (r2_hidden('#skF_1'(A_268, B_269, C_270), B_269) | k2_relset_1(A_268, B_269, C_270)=B_269 | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.15/1.73  tff(c_2033, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_52, c_2018])).
% 4.15/1.73  tff(c_2041, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_2033])).
% 4.15/1.73  tff(c_2042, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_171, c_2041])).
% 4.15/1.73  tff(c_60, plain, (![D_44]: (r2_hidden('#skF_6'(D_44), '#skF_3') | ~r2_hidden(D_44, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.15/1.73  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.15/1.73  tff(c_136, plain, (![A_67, B_68, C_69]: (k1_relset_1(A_67, B_68, C_69)=k1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.15/1.73  tff(c_145, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_136])).
% 4.15/1.73  tff(c_1747, plain, (![B_249, A_250, C_251]: (k1_xboole_0=B_249 | k1_relset_1(A_250, B_249, C_251)=A_250 | ~v1_funct_2(C_251, A_250, B_249) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_250, B_249))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.15/1.73  tff(c_1765, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_1747])).
% 4.15/1.73  tff(c_1773, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_145, c_1765])).
% 4.15/1.73  tff(c_1774, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1773])).
% 4.15/1.73  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.15/1.73  tff(c_89, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.15/1.73  tff(c_95, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_89])).
% 4.15/1.73  tff(c_99, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_95])).
% 4.15/1.73  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.15/1.73  tff(c_58, plain, (![D_44]: (k1_funct_1('#skF_5', '#skF_6'(D_44))=D_44 | ~r2_hidden(D_44, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.15/1.73  tff(c_1409, plain, (![A_213, C_214]: (r2_hidden(k4_tarski(A_213, k1_funct_1(C_214, A_213)), C_214) | ~r2_hidden(A_213, k1_relat_1(C_214)) | ~v1_funct_1(C_214) | ~v1_relat_1(C_214))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.15/1.73  tff(c_1421, plain, (![D_44]: (r2_hidden(k4_tarski('#skF_6'(D_44), D_44), '#skF_5') | ~r2_hidden('#skF_6'(D_44), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(D_44, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1409])).
% 4.15/1.73  tff(c_1427, plain, (![D_44]: (r2_hidden(k4_tarski('#skF_6'(D_44), D_44), '#skF_5') | ~r2_hidden('#skF_6'(D_44), k1_relat_1('#skF_5')) | ~r2_hidden(D_44, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_56, c_1421])).
% 4.15/1.73  tff(c_1776, plain, (![D_44]: (r2_hidden(k4_tarski('#skF_6'(D_44), D_44), '#skF_5') | ~r2_hidden('#skF_6'(D_44), '#skF_3') | ~r2_hidden(D_44, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1774, c_1427])).
% 4.15/1.73  tff(c_2133, plain, (![E_281, A_282, B_283, C_284]: (~r2_hidden(k4_tarski(E_281, '#skF_1'(A_282, B_283, C_284)), C_284) | k2_relset_1(A_282, B_283, C_284)=B_283 | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.15/1.73  tff(c_2139, plain, (![A_285, B_286]: (k2_relset_1(A_285, B_286, '#skF_5')=B_286 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))) | ~r2_hidden('#skF_6'('#skF_1'(A_285, B_286, '#skF_5')), '#skF_3') | ~r2_hidden('#skF_1'(A_285, B_286, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_1776, c_2133])).
% 4.15/1.73  tff(c_2285, plain, (![A_309, B_310]: (k2_relset_1(A_309, B_310, '#skF_5')=B_310 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))) | ~r2_hidden('#skF_1'(A_309, B_310, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_2139])).
% 4.15/1.73  tff(c_2298, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4' | ~r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_52, c_2285])).
% 4.15/1.73  tff(c_2306, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2042, c_170, c_2298])).
% 4.15/1.73  tff(c_2308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_2306])).
% 4.15/1.73  tff(c_2309, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1773])).
% 4.15/1.73  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.15/1.73  tff(c_2326, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2309, c_2])).
% 4.15/1.73  tff(c_2439, plain, (![A_319, B_320, C_321]: (r2_hidden('#skF_1'(A_319, B_320, C_321), B_320) | k2_relset_1(A_319, B_320, C_321)=B_320 | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(A_319, B_320))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.15/1.73  tff(c_2452, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_52, c_2439])).
% 4.15/1.73  tff(c_2459, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_2452])).
% 4.15/1.73  tff(c_2460, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_171, c_2459])).
% 4.15/1.73  tff(c_18, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.15/1.73  tff(c_2471, plain, (~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_2460, c_18])).
% 4.15/1.73  tff(c_2475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2326, c_2471])).
% 4.15/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.73  
% 4.15/1.73  Inference rules
% 4.15/1.73  ----------------------
% 4.15/1.73  #Ref     : 0
% 4.15/1.73  #Sup     : 447
% 4.15/1.73  #Fact    : 0
% 4.15/1.73  #Define  : 0
% 4.15/1.73  #Split   : 16
% 4.15/1.73  #Chain   : 0
% 4.15/1.73  #Close   : 0
% 4.15/1.73  
% 4.15/1.73  Ordering : KBO
% 4.15/1.73  
% 4.15/1.73  Simplification rules
% 4.15/1.73  ----------------------
% 4.15/1.73  #Subsume      : 88
% 4.15/1.73  #Demod        : 449
% 4.15/1.73  #Tautology    : 160
% 4.15/1.73  #SimpNegUnit  : 44
% 4.15/1.73  #BackRed      : 76
% 4.15/1.73  
% 4.15/1.73  #Partial instantiations: 0
% 4.15/1.73  #Strategies tried      : 1
% 4.15/1.73  
% 4.15/1.73  Timing (in seconds)
% 4.15/1.73  ----------------------
% 4.15/1.73  Preprocessing        : 0.33
% 4.15/1.73  Parsing              : 0.17
% 4.15/1.73  CNF conversion       : 0.02
% 4.15/1.73  Main loop            : 0.63
% 4.15/1.73  Inferencing          : 0.23
% 4.15/1.73  Reduction            : 0.20
% 4.15/1.73  Demodulation         : 0.14
% 4.15/1.73  BG Simplification    : 0.03
% 4.15/1.73  Subsumption          : 0.11
% 4.15/1.73  Abstraction          : 0.04
% 4.15/1.73  MUC search           : 0.00
% 4.15/1.73  Cooper               : 0.00
% 4.15/1.73  Total                : 0.99
% 4.15/1.73  Index Insertion      : 0.00
% 4.15/1.73  Index Deletion       : 0.00
% 4.15/1.73  Index Matching       : 0.00
% 4.15/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
