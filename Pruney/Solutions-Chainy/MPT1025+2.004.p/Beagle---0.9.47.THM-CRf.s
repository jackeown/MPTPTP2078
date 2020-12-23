%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:30 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 7.64s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 239 expanded)
%              Number of leaves         :   42 ( 100 expanded)
%              Depth                    :    9
%              Number of atoms          :  196 ( 609 expanded)
%              Number of equality atoms :   53 ( 146 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_148,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_111,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_129,axiom,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_93,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_22,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_219,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_226,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_70,c_219])).

tff(c_230,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_226])).

tff(c_605,plain,(
    ! [A_148,B_149,C_150,D_151] :
      ( k7_relset_1(A_148,B_149,C_150,D_151) = k9_relat_1(C_150,D_151)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_620,plain,(
    ! [D_151] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_151) = k9_relat_1('#skF_7',D_151) ),
    inference(resolution,[status(thm)],[c_70,c_605])).

tff(c_68,plain,(
    r2_hidden('#skF_8',k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_627,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_68])).

tff(c_72,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_379,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_399,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_379])).

tff(c_1077,plain,(
    ! [B_184,A_185,C_186] :
      ( k1_xboole_0 = B_184
      | k1_relset_1(A_185,B_184,C_186) = A_185
      | ~ v1_funct_2(C_186,A_185,B_184)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_185,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1088,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_1077])).

tff(c_1099,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_399,c_1088])).

tff(c_1101,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1099])).

tff(c_643,plain,(
    ! [A_153,B_154,C_155] :
      ( r2_hidden('#skF_2'(A_153,B_154,C_155),k1_relat_1(C_155))
      | ~ r2_hidden(A_153,k9_relat_1(C_155,B_154))
      | ~ v1_relat_1(C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2164,plain,(
    ! [A_287,B_288,C_289] :
      ( m1_subset_1('#skF_2'(A_287,B_288,C_289),k1_relat_1(C_289))
      | ~ r2_hidden(A_287,k9_relat_1(C_289,B_288))
      | ~ v1_relat_1(C_289) ) ),
    inference(resolution,[status(thm)],[c_643,c_16])).

tff(c_2167,plain,(
    ! [A_287,B_288] :
      ( m1_subset_1('#skF_2'(A_287,B_288,'#skF_7'),'#skF_4')
      | ~ r2_hidden(A_287,k9_relat_1('#skF_7',B_288))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1101,c_2164])).

tff(c_3282,plain,(
    ! [A_385,B_386] :
      ( m1_subset_1('#skF_2'(A_385,B_386,'#skF_7'),'#skF_4')
      | ~ r2_hidden(A_385,k9_relat_1('#skF_7',B_386)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_2167])).

tff(c_3325,plain,(
    m1_subset_1('#skF_2'('#skF_8','#skF_6','#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_627,c_3282])).

tff(c_74,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_924,plain,(
    ! [A_176,B_177,C_178] :
      ( r2_hidden(k4_tarski('#skF_2'(A_176,B_177,C_178),A_176),C_178)
      | ~ r2_hidden(A_176,k9_relat_1(C_178,B_177))
      | ~ v1_relat_1(C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_46,plain,(
    ! [C_34,A_32,B_33] :
      ( k1_funct_1(C_34,A_32) = B_33
      | ~ r2_hidden(k4_tarski(A_32,B_33),C_34)
      | ~ v1_funct_1(C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2781,plain,(
    ! [C_338,A_339,B_340] :
      ( k1_funct_1(C_338,'#skF_2'(A_339,B_340,C_338)) = A_339
      | ~ v1_funct_1(C_338)
      | ~ r2_hidden(A_339,k9_relat_1(C_338,B_340))
      | ~ v1_relat_1(C_338) ) ),
    inference(resolution,[status(thm)],[c_924,c_46])).

tff(c_2794,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_8','#skF_6','#skF_7')) = '#skF_8'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_627,c_2781])).

tff(c_2810,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_8','#skF_6','#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_74,c_2794])).

tff(c_447,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_hidden('#skF_2'(A_109,B_110,C_111),B_110)
      | ~ r2_hidden(A_109,k9_relat_1(C_111,B_110))
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_66,plain,(
    ! [F_49] :
      ( k1_funct_1('#skF_7',F_49) != '#skF_8'
      | ~ r2_hidden(F_49,'#skF_6')
      | ~ m1_subset_1(F_49,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_465,plain,(
    ! [A_109,C_111] :
      ( k1_funct_1('#skF_7','#skF_2'(A_109,'#skF_6',C_111)) != '#skF_8'
      | ~ m1_subset_1('#skF_2'(A_109,'#skF_6',C_111),'#skF_4')
      | ~ r2_hidden(A_109,k9_relat_1(C_111,'#skF_6'))
      | ~ v1_relat_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_447,c_66])).

tff(c_666,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_8','#skF_6','#skF_7')) != '#skF_8'
    | ~ m1_subset_1('#skF_2'('#skF_8','#skF_6','#skF_7'),'#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_627,c_465])).

tff(c_685,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_8','#skF_6','#skF_7')) != '#skF_8'
    | ~ m1_subset_1('#skF_2'('#skF_8','#skF_6','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_666])).

tff(c_5758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3325,c_2810,c_685])).

tff(c_5759,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1099])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [A_26] : k1_relat_1('#skF_3'(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_42,plain,(
    ! [A_26] : v1_relat_1('#skF_3'(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_135,plain,(
    ! [A_63] :
      ( k1_relat_1(A_63) != k1_xboole_0
      | k1_xboole_0 = A_63
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_144,plain,(
    ! [A_26] :
      ( k1_relat_1('#skF_3'(A_26)) != k1_xboole_0
      | '#skF_3'(A_26) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_135])).

tff(c_149,plain,(
    ! [A_26] :
      ( k1_xboole_0 != A_26
      | '#skF_3'(A_26) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_144])).

tff(c_40,plain,(
    ! [A_26] : v1_funct_1('#skF_3'(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    ! [A_26,C_31] :
      ( k1_funct_1('#skF_3'(A_26),C_31) = k1_xboole_0
      | ~ r2_hidden(C_31,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_748,plain,(
    ! [A_166,C_167] :
      ( r2_hidden(k4_tarski(A_166,k1_funct_1(C_167,A_166)),C_167)
      | ~ r2_hidden(A_166,k1_relat_1(C_167))
      | ~ v1_funct_1(C_167)
      | ~ v1_relat_1(C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_794,plain,(
    ! [C_31,A_26] :
      ( r2_hidden(k4_tarski(C_31,k1_xboole_0),'#skF_3'(A_26))
      | ~ r2_hidden(C_31,k1_relat_1('#skF_3'(A_26)))
      | ~ v1_funct_1('#skF_3'(A_26))
      | ~ v1_relat_1('#skF_3'(A_26))
      | ~ r2_hidden(C_31,A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_748])).

tff(c_827,plain,(
    ! [C_169,A_170] :
      ( r2_hidden(k4_tarski(C_169,k1_xboole_0),'#skF_3'(A_170))
      | ~ r2_hidden(C_169,A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_794])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_858,plain,(
    ! [A_171,C_172] :
      ( ~ v1_xboole_0('#skF_3'(A_171))
      | ~ r2_hidden(C_172,A_171) ) ),
    inference(resolution,[status(thm)],[c_827,c_2])).

tff(c_860,plain,(
    ! [C_172,A_26] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_172,A_26)
      | k1_xboole_0 != A_26 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_858])).

tff(c_864,plain,(
    ! [C_173,A_174] :
      ( ~ r2_hidden(C_173,A_174)
      | k1_xboole_0 != A_174 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_860])).

tff(c_892,plain,(
    ! [A_1] :
      ( k1_xboole_0 != A_1
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_864])).

tff(c_5903,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5759,c_892])).

tff(c_10,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5798,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5759,c_5759,c_10])).

tff(c_310,plain,(
    ! [C_84,A_85,B_86] :
      ( r2_hidden(C_84,A_85)
      | ~ r2_hidden(C_84,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_317,plain,(
    ! [A_87,A_88] :
      ( r2_hidden('#skF_1'(A_87),A_88)
      | ~ m1_subset_1(A_87,k1_zfmisc_1(A_88))
      | v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_4,c_310])).

tff(c_338,plain,(
    ! [A_89,A_90] :
      ( ~ v1_xboole_0(A_89)
      | ~ m1_subset_1(A_90,k1_zfmisc_1(A_89))
      | v1_xboole_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_317,c_2])).

tff(c_347,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_338])).

tff(c_348,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_347])).

tff(c_5826,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5798,c_348])).

tff(c_5906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5903,c_5826])).

tff(c_5907,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_347])).

tff(c_6247,plain,(
    ! [A_705,B_706,C_707,D_708] :
      ( k7_relset_1(A_705,B_706,C_707,D_708) = k9_relat_1(C_707,D_708)
      | ~ m1_subset_1(C_707,k1_zfmisc_1(k2_zfmisc_1(A_705,B_706))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6262,plain,(
    ! [D_708] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_708) = k9_relat_1('#skF_7',D_708) ),
    inference(resolution,[status(thm)],[c_70,c_6247])).

tff(c_6267,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6262,c_68])).

tff(c_6328,plain,(
    ! [A_710,B_711,C_712] :
      ( r2_hidden(k4_tarski('#skF_2'(A_710,B_711,C_712),A_710),C_712)
      | ~ r2_hidden(A_710,k9_relat_1(C_712,B_711))
      | ~ v1_relat_1(C_712) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6396,plain,(
    ! [C_714,A_715,B_716] :
      ( ~ v1_xboole_0(C_714)
      | ~ r2_hidden(A_715,k9_relat_1(C_714,B_716))
      | ~ v1_relat_1(C_714) ) ),
    inference(resolution,[status(thm)],[c_6328,c_2])).

tff(c_6403,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6267,c_6396])).

tff(c_6420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_5907,c_6403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.30  % Computer   : n011.cluster.edu
% 0.12/0.30  % Model      : x86_64 x86_64
% 0.12/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.30  % Memory     : 8042.1875MB
% 0.12/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.30  % CPULimit   : 60
% 0.12/0.30  % DateTime   : Tue Dec  1 11:01:42 EST 2020
% 0.12/0.30  % CPUTime    : 
% 0.12/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.64/2.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.64/2.52  
% 7.64/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.64/2.52  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_3
% 7.64/2.52  
% 7.64/2.52  %Foreground sorts:
% 7.64/2.52  
% 7.64/2.52  
% 7.64/2.52  %Background operators:
% 7.64/2.52  
% 7.64/2.52  
% 7.64/2.52  %Foreground operators:
% 7.64/2.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.64/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.64/2.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.64/2.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.64/2.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.64/2.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.64/2.52  tff('#skF_7', type, '#skF_7': $i).
% 7.64/2.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.64/2.52  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.64/2.52  tff('#skF_5', type, '#skF_5': $i).
% 7.64/2.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.64/2.52  tff('#skF_6', type, '#skF_6': $i).
% 7.64/2.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.64/2.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.64/2.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.64/2.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.64/2.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.64/2.52  tff('#skF_8', type, '#skF_8': $i).
% 7.64/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.64/2.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.64/2.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.64/2.52  tff('#skF_4', type, '#skF_4': $i).
% 7.64/2.52  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.64/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.64/2.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.64/2.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.64/2.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.64/2.52  
% 7.64/2.54  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.64/2.54  tff(f_148, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 7.64/2.54  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.64/2.54  tff(f_111, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 7.64/2.54  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.64/2.54  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.64/2.54  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 7.64/2.54  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 7.64/2.54  tff(f_103, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 7.64/2.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.64/2.54  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.64/2.54  tff(f_93, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 7.64/2.54  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 7.64/2.54  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.64/2.54  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 7.64/2.54  tff(c_22, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.64/2.54  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.64/2.54  tff(c_219, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.64/2.54  tff(c_226, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_70, c_219])).
% 7.64/2.54  tff(c_230, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_226])).
% 7.64/2.54  tff(c_605, plain, (![A_148, B_149, C_150, D_151]: (k7_relset_1(A_148, B_149, C_150, D_151)=k9_relat_1(C_150, D_151) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.64/2.54  tff(c_620, plain, (![D_151]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_151)=k9_relat_1('#skF_7', D_151))), inference(resolution, [status(thm)], [c_70, c_605])).
% 7.64/2.54  tff(c_68, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.64/2.54  tff(c_627, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_620, c_68])).
% 7.64/2.54  tff(c_72, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.64/2.54  tff(c_379, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.64/2.54  tff(c_399, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_379])).
% 7.64/2.54  tff(c_1077, plain, (![B_184, A_185, C_186]: (k1_xboole_0=B_184 | k1_relset_1(A_185, B_184, C_186)=A_185 | ~v1_funct_2(C_186, A_185, B_184) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_185, B_184))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.64/2.54  tff(c_1088, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_1077])).
% 7.64/2.54  tff(c_1099, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_399, c_1088])).
% 7.64/2.54  tff(c_1101, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_1099])).
% 7.64/2.54  tff(c_643, plain, (![A_153, B_154, C_155]: (r2_hidden('#skF_2'(A_153, B_154, C_155), k1_relat_1(C_155)) | ~r2_hidden(A_153, k9_relat_1(C_155, B_154)) | ~v1_relat_1(C_155))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.64/2.54  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.64/2.54  tff(c_2164, plain, (![A_287, B_288, C_289]: (m1_subset_1('#skF_2'(A_287, B_288, C_289), k1_relat_1(C_289)) | ~r2_hidden(A_287, k9_relat_1(C_289, B_288)) | ~v1_relat_1(C_289))), inference(resolution, [status(thm)], [c_643, c_16])).
% 7.64/2.54  tff(c_2167, plain, (![A_287, B_288]: (m1_subset_1('#skF_2'(A_287, B_288, '#skF_7'), '#skF_4') | ~r2_hidden(A_287, k9_relat_1('#skF_7', B_288)) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1101, c_2164])).
% 7.64/2.54  tff(c_3282, plain, (![A_385, B_386]: (m1_subset_1('#skF_2'(A_385, B_386, '#skF_7'), '#skF_4') | ~r2_hidden(A_385, k9_relat_1('#skF_7', B_386)))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_2167])).
% 7.64/2.54  tff(c_3325, plain, (m1_subset_1('#skF_2'('#skF_8', '#skF_6', '#skF_7'), '#skF_4')), inference(resolution, [status(thm)], [c_627, c_3282])).
% 7.64/2.54  tff(c_74, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.64/2.54  tff(c_924, plain, (![A_176, B_177, C_178]: (r2_hidden(k4_tarski('#skF_2'(A_176, B_177, C_178), A_176), C_178) | ~r2_hidden(A_176, k9_relat_1(C_178, B_177)) | ~v1_relat_1(C_178))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.64/2.54  tff(c_46, plain, (![C_34, A_32, B_33]: (k1_funct_1(C_34, A_32)=B_33 | ~r2_hidden(k4_tarski(A_32, B_33), C_34) | ~v1_funct_1(C_34) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.64/2.54  tff(c_2781, plain, (![C_338, A_339, B_340]: (k1_funct_1(C_338, '#skF_2'(A_339, B_340, C_338))=A_339 | ~v1_funct_1(C_338) | ~r2_hidden(A_339, k9_relat_1(C_338, B_340)) | ~v1_relat_1(C_338))), inference(resolution, [status(thm)], [c_924, c_46])).
% 7.64/2.54  tff(c_2794, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_8', '#skF_6', '#skF_7'))='#skF_8' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_627, c_2781])).
% 7.64/2.54  tff(c_2810, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_8', '#skF_6', '#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_230, c_74, c_2794])).
% 7.64/2.54  tff(c_447, plain, (![A_109, B_110, C_111]: (r2_hidden('#skF_2'(A_109, B_110, C_111), B_110) | ~r2_hidden(A_109, k9_relat_1(C_111, B_110)) | ~v1_relat_1(C_111))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.64/2.54  tff(c_66, plain, (![F_49]: (k1_funct_1('#skF_7', F_49)!='#skF_8' | ~r2_hidden(F_49, '#skF_6') | ~m1_subset_1(F_49, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.64/2.54  tff(c_465, plain, (![A_109, C_111]: (k1_funct_1('#skF_7', '#skF_2'(A_109, '#skF_6', C_111))!='#skF_8' | ~m1_subset_1('#skF_2'(A_109, '#skF_6', C_111), '#skF_4') | ~r2_hidden(A_109, k9_relat_1(C_111, '#skF_6')) | ~v1_relat_1(C_111))), inference(resolution, [status(thm)], [c_447, c_66])).
% 7.64/2.54  tff(c_666, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_8', '#skF_6', '#skF_7'))!='#skF_8' | ~m1_subset_1('#skF_2'('#skF_8', '#skF_6', '#skF_7'), '#skF_4') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_627, c_465])).
% 7.64/2.54  tff(c_685, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_8', '#skF_6', '#skF_7'))!='#skF_8' | ~m1_subset_1('#skF_2'('#skF_8', '#skF_6', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_666])).
% 7.64/2.54  tff(c_5758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3325, c_2810, c_685])).
% 7.64/2.54  tff(c_5759, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1099])).
% 7.64/2.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.64/2.54  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.64/2.54  tff(c_38, plain, (![A_26]: (k1_relat_1('#skF_3'(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.64/2.54  tff(c_42, plain, (![A_26]: (v1_relat_1('#skF_3'(A_26)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.64/2.54  tff(c_135, plain, (![A_63]: (k1_relat_1(A_63)!=k1_xboole_0 | k1_xboole_0=A_63 | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.64/2.54  tff(c_144, plain, (![A_26]: (k1_relat_1('#skF_3'(A_26))!=k1_xboole_0 | '#skF_3'(A_26)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_135])).
% 7.64/2.54  tff(c_149, plain, (![A_26]: (k1_xboole_0!=A_26 | '#skF_3'(A_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_144])).
% 7.64/2.54  tff(c_40, plain, (![A_26]: (v1_funct_1('#skF_3'(A_26)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.64/2.54  tff(c_36, plain, (![A_26, C_31]: (k1_funct_1('#skF_3'(A_26), C_31)=k1_xboole_0 | ~r2_hidden(C_31, A_26))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.64/2.54  tff(c_748, plain, (![A_166, C_167]: (r2_hidden(k4_tarski(A_166, k1_funct_1(C_167, A_166)), C_167) | ~r2_hidden(A_166, k1_relat_1(C_167)) | ~v1_funct_1(C_167) | ~v1_relat_1(C_167))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.64/2.54  tff(c_794, plain, (![C_31, A_26]: (r2_hidden(k4_tarski(C_31, k1_xboole_0), '#skF_3'(A_26)) | ~r2_hidden(C_31, k1_relat_1('#skF_3'(A_26))) | ~v1_funct_1('#skF_3'(A_26)) | ~v1_relat_1('#skF_3'(A_26)) | ~r2_hidden(C_31, A_26))), inference(superposition, [status(thm), theory('equality')], [c_36, c_748])).
% 7.64/2.54  tff(c_827, plain, (![C_169, A_170]: (r2_hidden(k4_tarski(C_169, k1_xboole_0), '#skF_3'(A_170)) | ~r2_hidden(C_169, A_170))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_794])).
% 7.64/2.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.64/2.54  tff(c_858, plain, (![A_171, C_172]: (~v1_xboole_0('#skF_3'(A_171)) | ~r2_hidden(C_172, A_171))), inference(resolution, [status(thm)], [c_827, c_2])).
% 7.64/2.54  tff(c_860, plain, (![C_172, A_26]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_172, A_26) | k1_xboole_0!=A_26)), inference(superposition, [status(thm), theory('equality')], [c_149, c_858])).
% 7.64/2.54  tff(c_864, plain, (![C_173, A_174]: (~r2_hidden(C_173, A_174) | k1_xboole_0!=A_174)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_860])).
% 7.64/2.54  tff(c_892, plain, (![A_1]: (k1_xboole_0!=A_1 | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_864])).
% 7.64/2.54  tff(c_5903, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5759, c_892])).
% 7.64/2.54  tff(c_10, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.64/2.54  tff(c_5798, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5759, c_5759, c_10])).
% 7.64/2.54  tff(c_310, plain, (![C_84, A_85, B_86]: (r2_hidden(C_84, A_85) | ~r2_hidden(C_84, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.64/2.54  tff(c_317, plain, (![A_87, A_88]: (r2_hidden('#skF_1'(A_87), A_88) | ~m1_subset_1(A_87, k1_zfmisc_1(A_88)) | v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_4, c_310])).
% 7.64/2.54  tff(c_338, plain, (![A_89, A_90]: (~v1_xboole_0(A_89) | ~m1_subset_1(A_90, k1_zfmisc_1(A_89)) | v1_xboole_0(A_90))), inference(resolution, [status(thm)], [c_317, c_2])).
% 7.64/2.54  tff(c_347, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_70, c_338])).
% 7.64/2.54  tff(c_348, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_347])).
% 7.64/2.54  tff(c_5826, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5798, c_348])).
% 7.64/2.54  tff(c_5906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5903, c_5826])).
% 7.64/2.54  tff(c_5907, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_347])).
% 7.64/2.54  tff(c_6247, plain, (![A_705, B_706, C_707, D_708]: (k7_relset_1(A_705, B_706, C_707, D_708)=k9_relat_1(C_707, D_708) | ~m1_subset_1(C_707, k1_zfmisc_1(k2_zfmisc_1(A_705, B_706))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.64/2.54  tff(c_6262, plain, (![D_708]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_708)=k9_relat_1('#skF_7', D_708))), inference(resolution, [status(thm)], [c_70, c_6247])).
% 7.64/2.54  tff(c_6267, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6262, c_68])).
% 7.64/2.54  tff(c_6328, plain, (![A_710, B_711, C_712]: (r2_hidden(k4_tarski('#skF_2'(A_710, B_711, C_712), A_710), C_712) | ~r2_hidden(A_710, k9_relat_1(C_712, B_711)) | ~v1_relat_1(C_712))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.64/2.54  tff(c_6396, plain, (![C_714, A_715, B_716]: (~v1_xboole_0(C_714) | ~r2_hidden(A_715, k9_relat_1(C_714, B_716)) | ~v1_relat_1(C_714))), inference(resolution, [status(thm)], [c_6328, c_2])).
% 7.64/2.54  tff(c_6403, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6267, c_6396])).
% 7.64/2.54  tff(c_6420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_230, c_5907, c_6403])).
% 7.64/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.64/2.54  
% 7.64/2.54  Inference rules
% 7.64/2.54  ----------------------
% 7.64/2.54  #Ref     : 1
% 7.64/2.54  #Sup     : 1295
% 7.64/2.54  #Fact    : 0
% 7.64/2.54  #Define  : 0
% 7.64/2.54  #Split   : 28
% 7.64/2.54  #Chain   : 0
% 7.64/2.54  #Close   : 0
% 7.64/2.54  
% 7.64/2.54  Ordering : KBO
% 7.64/2.54  
% 7.64/2.54  Simplification rules
% 7.64/2.54  ----------------------
% 7.64/2.54  #Subsume      : 337
% 7.64/2.54  #Demod        : 396
% 7.64/2.54  #Tautology    : 115
% 7.64/2.54  #SimpNegUnit  : 50
% 7.64/2.54  #BackRed      : 73
% 7.64/2.54  
% 7.64/2.54  #Partial instantiations: 0
% 7.64/2.54  #Strategies tried      : 1
% 7.64/2.54  
% 7.64/2.54  Timing (in seconds)
% 7.64/2.54  ----------------------
% 7.64/2.54  Preprocessing        : 0.36
% 7.64/2.54  Parsing              : 0.19
% 7.64/2.54  CNF conversion       : 0.03
% 7.64/2.54  Main loop            : 1.47
% 7.64/2.54  Inferencing          : 0.48
% 7.64/2.54  Reduction            : 0.43
% 7.64/2.54  Demodulation         : 0.29
% 7.64/2.54  BG Simplification    : 0.05
% 7.64/2.54  Subsumption          : 0.39
% 7.64/2.54  Abstraction          : 0.06
% 7.64/2.54  MUC search           : 0.00
% 7.64/2.54  Cooper               : 0.00
% 7.64/2.54  Total                : 1.87
% 7.64/2.54  Index Insertion      : 0.00
% 7.64/2.54  Index Deletion       : 0.00
% 7.64/2.54  Index Matching       : 0.00
% 7.64/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
