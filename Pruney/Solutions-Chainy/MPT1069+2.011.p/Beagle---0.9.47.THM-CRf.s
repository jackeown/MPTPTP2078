%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:46 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 448 expanded)
%              Number of leaves         :   40 ( 174 expanded)
%              Depth                    :   16
%              Number of atoms          :  338 (1793 expanded)
%              Number of equality atoms :   68 ( 341 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_172,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_147,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(k2_relset_1(A,B,D),C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_50,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_112,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_119,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_112])).

tff(c_48,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_121,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_48])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_571,plain,(
    ! [C_170,F_167,D_168,A_166,E_169,B_165] :
      ( k1_funct_1(k8_funct_2(B_165,C_170,A_166,D_168,E_169),F_167) = k1_funct_1(E_169,k1_funct_1(D_168,F_167))
      | k1_xboole_0 = B_165
      | ~ r1_tarski(k2_relset_1(B_165,C_170,D_168),k1_relset_1(C_170,A_166,E_169))
      | ~ m1_subset_1(F_167,B_165)
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(C_170,A_166)))
      | ~ v1_funct_1(E_169)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_zfmisc_1(B_165,C_170)))
      | ~ v1_funct_2(D_168,B_165,C_170)
      | ~ v1_funct_1(D_168)
      | v1_xboole_0(C_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_577,plain,(
    ! [B_165,D_168,F_167] :
      ( k1_funct_1(k8_funct_2(B_165,'#skF_3','#skF_1',D_168,'#skF_5'),F_167) = k1_funct_1('#skF_5',k1_funct_1(D_168,F_167))
      | k1_xboole_0 = B_165
      | ~ r1_tarski(k2_relset_1(B_165,'#skF_3',D_168),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_167,B_165)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_zfmisc_1(B_165,'#skF_3')))
      | ~ v1_funct_2(D_168,B_165,'#skF_3')
      | ~ v1_funct_1(D_168)
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_571])).

tff(c_585,plain,(
    ! [B_165,D_168,F_167] :
      ( k1_funct_1(k8_funct_2(B_165,'#skF_3','#skF_1',D_168,'#skF_5'),F_167) = k1_funct_1('#skF_5',k1_funct_1(D_168,F_167))
      | k1_xboole_0 = B_165
      | ~ r1_tarski(k2_relset_1(B_165,'#skF_3',D_168),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_167,B_165)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_zfmisc_1(B_165,'#skF_3')))
      | ~ v1_funct_2(D_168,B_165,'#skF_3')
      | ~ v1_funct_1(D_168)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_577])).

tff(c_597,plain,(
    ! [B_176,D_177,F_178] :
      ( k1_funct_1(k8_funct_2(B_176,'#skF_3','#skF_1',D_177,'#skF_5'),F_178) = k1_funct_1('#skF_5',k1_funct_1(D_177,F_178))
      | k1_xboole_0 = B_176
      | ~ r1_tarski(k2_relset_1(B_176,'#skF_3',D_177),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_178,B_176)
      | ~ m1_subset_1(D_177,k1_zfmisc_1(k2_zfmisc_1(B_176,'#skF_3')))
      | ~ v1_funct_2(D_177,B_176,'#skF_3')
      | ~ v1_funct_1(D_177) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_585])).

tff(c_599,plain,(
    ! [F_178] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_178) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_178))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_178,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_121,c_597])).

tff(c_602,plain,(
    ! [F_178] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_178) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_178))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_178,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_599])).

tff(c_604,plain,(
    ! [F_179] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_179) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_179))
      | ~ m1_subset_1(F_179,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_602])).

tff(c_84,plain,(
    ! [C_69,B_70,A_71] :
      ( v5_relat_1(C_69,B_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_91,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_84])).

tff(c_75,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_82,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_75])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_369,plain,(
    ! [D_123,C_124,B_125,A_126] :
      ( r2_hidden(k1_funct_1(D_123,C_124),B_125)
      | k1_xboole_0 = B_125
      | ~ r2_hidden(C_124,A_126)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125)))
      | ~ v1_funct_2(D_123,A_126,B_125)
      | ~ v1_funct_1(D_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_381,plain,(
    ! [D_134,A_135,B_136,B_137] :
      ( r2_hidden(k1_funct_1(D_134,A_135),B_136)
      | k1_xboole_0 = B_136
      | ~ m1_subset_1(D_134,k1_zfmisc_1(k2_zfmisc_1(B_137,B_136)))
      | ~ v1_funct_2(D_134,B_137,B_136)
      | ~ v1_funct_1(D_134)
      | v1_xboole_0(B_137)
      | ~ m1_subset_1(A_135,B_137) ) ),
    inference(resolution,[status(thm)],[c_6,c_369])).

tff(c_385,plain,(
    ! [A_135] :
      ( r2_hidden(k1_funct_1('#skF_4',A_135),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_135,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_381])).

tff(c_392,plain,(
    ! [A_135] :
      ( r2_hidden(k1_funct_1('#skF_4',A_135),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_135,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_385])).

tff(c_393,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_392])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_396,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_393,c_4])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_396])).

tff(c_405,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_392])).

tff(c_373,plain,(
    ! [B_127,D_128,A_129,C_130] :
      ( k1_xboole_0 = B_127
      | v1_funct_2(D_128,A_129,C_130)
      | ~ r1_tarski(k2_relset_1(A_129,B_127,D_128),C_130)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_127)))
      | ~ v1_funct_2(D_128,A_129,B_127)
      | ~ v1_funct_1(D_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_375,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_121,c_373])).

tff(c_378,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_375])).

tff(c_379,plain,(
    v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_406,plain,(
    ! [B_138,D_139,A_140,C_141] :
      ( k1_xboole_0 = B_138
      | m1_subset_1(D_139,k1_zfmisc_1(k2_zfmisc_1(A_140,C_141)))
      | ~ r1_tarski(k2_relset_1(A_140,B_138,D_139),C_141)
      | ~ m1_subset_1(D_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_138)))
      | ~ v1_funct_2(D_139,A_140,B_138)
      | ~ v1_funct_1(D_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_408,plain,
    ( k1_xboole_0 = '#skF_3'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_121,c_406])).

tff(c_411,plain,
    ( k1_xboole_0 = '#skF_3'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_408])).

tff(c_412,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_372,plain,(
    ! [D_123,A_2,B_125,B_3] :
      ( r2_hidden(k1_funct_1(D_123,A_2),B_125)
      | k1_xboole_0 = B_125
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(B_3,B_125)))
      | ~ v1_funct_2(D_123,B_3,B_125)
      | ~ v1_funct_1(D_123)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_369])).

tff(c_414,plain,(
    ! [A_2] :
      ( r2_hidden(k1_funct_1('#skF_4',A_2),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_2,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_412,c_372])).

tff(c_435,plain,(
    ! [A_2] :
      ( r2_hidden(k1_funct_1('#skF_4',A_2),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_2,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_379,c_414])).

tff(c_436,plain,(
    ! [A_2] :
      ( r2_hidden(k1_funct_1('#skF_4',A_2),k1_relat_1('#skF_5'))
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ m1_subset_1(A_2,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_405,c_435])).

tff(c_481,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_436])).

tff(c_130,plain,(
    ! [C_81,A_82,B_83] :
      ( ~ v1_xboole_0(C_81)
      | ~ v1_funct_2(C_81,A_82,B_83)
      | ~ v1_funct_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | v1_xboole_0(B_83)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_136,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_130])).

tff(c_143,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_136])).

tff(c_144,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_143])).

tff(c_145,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_227,plain,(
    ! [D_97,C_98,B_99,A_100] :
      ( r2_hidden(k1_funct_1(D_97,C_98),B_99)
      | k1_xboole_0 = B_99
      | ~ r2_hidden(C_98,A_100)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99)))
      | ~ v1_funct_2(D_97,A_100,B_99)
      | ~ v1_funct_1(D_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_239,plain,(
    ! [D_108,A_109,B_110,B_111] :
      ( r2_hidden(k1_funct_1(D_108,A_109),B_110)
      | k1_xboole_0 = B_110
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_zfmisc_1(B_111,B_110)))
      | ~ v1_funct_2(D_108,B_111,B_110)
      | ~ v1_funct_1(D_108)
      | v1_xboole_0(B_111)
      | ~ m1_subset_1(A_109,B_111) ) ),
    inference(resolution,[status(thm)],[c_6,c_227])).

tff(c_243,plain,(
    ! [A_109] :
      ( r2_hidden(k1_funct_1('#skF_4',A_109),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_109,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_239])).

tff(c_250,plain,(
    ! [A_109] :
      ( r2_hidden(k1_funct_1('#skF_4',A_109),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_109,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_243])).

tff(c_251,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_254,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_251,c_4])).

tff(c_261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_254])).

tff(c_262,plain,(
    ! [A_109] :
      ( k1_xboole_0 = '#skF_3'
      | r2_hidden(k1_funct_1('#skF_4',A_109),'#skF_3')
      | ~ m1_subset_1(A_109,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_264,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_280,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_2])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_280])).

tff(c_286,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_147,plain,(
    ! [A_84,B_85,C_86] :
      ( k7_partfun1(A_84,B_85,C_86) = k1_funct_1(B_85,C_86)
      | ~ r2_hidden(C_86,k1_relat_1(B_85))
      | ~ v1_funct_1(B_85)
      | ~ v5_relat_1(B_85,A_84)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_152,plain,(
    ! [A_87,B_88,A_89] :
      ( k7_partfun1(A_87,B_88,A_89) = k1_funct_1(B_88,A_89)
      | ~ v1_funct_1(B_88)
      | ~ v5_relat_1(B_88,A_87)
      | ~ v1_relat_1(B_88)
      | v1_xboole_0(k1_relat_1(B_88))
      | ~ m1_subset_1(A_89,k1_relat_1(B_88)) ) ),
    inference(resolution,[status(thm)],[c_6,c_147])).

tff(c_154,plain,(
    ! [A_89] :
      ( k7_partfun1('#skF_1','#skF_5',A_89) = k1_funct_1('#skF_5',A_89)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_89,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_91,c_152])).

tff(c_159,plain,(
    ! [A_89] :
      ( k7_partfun1('#skF_1','#skF_5',A_89) = k1_funct_1('#skF_5',A_89)
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_89,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_54,c_154])).

tff(c_163,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_171,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_163,c_4])).

tff(c_182,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_121])).

tff(c_291,plain,(
    ! [B_113,D_114,A_115,C_116] :
      ( k1_xboole_0 = B_113
      | m1_subset_1(D_114,k1_zfmisc_1(k2_zfmisc_1(A_115,C_116)))
      | ~ r1_tarski(k2_relset_1(A_115,B_113,D_114),C_116)
      | ~ m1_subset_1(D_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_113)))
      | ~ v1_funct_2(D_114,A_115,B_113)
      | ~ v1_funct_1(D_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_293,plain,
    ( k1_xboole_0 = '#skF_3'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_xboole_0)))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_182,c_291])).

tff(c_296,plain,
    ( k1_xboole_0 = '#skF_3'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_293])).

tff(c_297,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_xboole_0))) ),
    inference(negUnitSimplification,[status(thm)],[c_286,c_296])).

tff(c_16,plain,(
    ! [C_14,B_12,A_11] :
      ( v1_xboole_0(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(B_12,A_11)))
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_308,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_297,c_16])).

tff(c_331,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_308])).

tff(c_333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_331])).

tff(c_335,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_503,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_335])).

tff(c_508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_503])).

tff(c_511,plain,(
    ! [A_149] :
      ( r2_hidden(k1_funct_1('#skF_4',A_149),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_149,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_26,plain,(
    ! [A_22,B_23,C_25] :
      ( k7_partfun1(A_22,B_23,C_25) = k1_funct_1(B_23,C_25)
      | ~ r2_hidden(C_25,k1_relat_1(B_23))
      | ~ v1_funct_1(B_23)
      | ~ v5_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_515,plain,(
    ! [A_22,A_149] :
      ( k7_partfun1(A_22,'#skF_5',k1_funct_1('#skF_4',A_149)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_149))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_22)
      | ~ v1_relat_1('#skF_5')
      | ~ m1_subset_1(A_149,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_511,c_26])).

tff(c_533,plain,(
    ! [A_153,A_154] :
      ( k7_partfun1(A_153,'#skF_5',k1_funct_1('#skF_4',A_154)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_154))
      | ~ v5_relat_1('#skF_5',A_153)
      | ~ m1_subset_1(A_154,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_54,c_515])).

tff(c_44,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_539,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v5_relat_1('#skF_5','#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_44])).

tff(c_545,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_91,c_539])).

tff(c_618,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_545])).

tff(c_630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_618])).

tff(c_631,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_644,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_2])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_644])).

tff(c_648,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_658,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_2])).

tff(c_661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_658])).

tff(c_662,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_666,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_662,c_4])).

tff(c_673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:55:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.49  
% 3.17/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.17/1.50  
% 3.17/1.50  %Foreground sorts:
% 3.17/1.50  
% 3.17/1.50  
% 3.17/1.50  %Background operators:
% 3.17/1.50  
% 3.17/1.50  
% 3.17/1.50  %Foreground operators:
% 3.17/1.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.17/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.17/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.50  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.17/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.17/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.17/1.50  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.17/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.17/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.17/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.17/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.17/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.17/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.17/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.17/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.17/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.17/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.17/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.50  
% 3.17/1.52  tff(f_172, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 3.17/1.52  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.17/1.52  tff(f_116, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 3.17/1.52  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.17/1.52  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.17/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.17/1.52  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.17/1.52  tff(f_128, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.17/1.52  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.17/1.52  tff(f_147, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 3.17/1.52  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 3.17/1.52  tff(f_92, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 3.17/1.52  tff(f_57, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.17/1.52  tff(c_46, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.17/1.52  tff(c_62, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.17/1.52  tff(c_50, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.17/1.52  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.17/1.52  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.17/1.52  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.17/1.52  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.17/1.52  tff(c_112, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.17/1.52  tff(c_119, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_112])).
% 3.17/1.52  tff(c_48, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.17/1.52  tff(c_121, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_48])).
% 3.17/1.52  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.17/1.52  tff(c_571, plain, (![C_170, F_167, D_168, A_166, E_169, B_165]: (k1_funct_1(k8_funct_2(B_165, C_170, A_166, D_168, E_169), F_167)=k1_funct_1(E_169, k1_funct_1(D_168, F_167)) | k1_xboole_0=B_165 | ~r1_tarski(k2_relset_1(B_165, C_170, D_168), k1_relset_1(C_170, A_166, E_169)) | ~m1_subset_1(F_167, B_165) | ~m1_subset_1(E_169, k1_zfmisc_1(k2_zfmisc_1(C_170, A_166))) | ~v1_funct_1(E_169) | ~m1_subset_1(D_168, k1_zfmisc_1(k2_zfmisc_1(B_165, C_170))) | ~v1_funct_2(D_168, B_165, C_170) | ~v1_funct_1(D_168) | v1_xboole_0(C_170))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.17/1.52  tff(c_577, plain, (![B_165, D_168, F_167]: (k1_funct_1(k8_funct_2(B_165, '#skF_3', '#skF_1', D_168, '#skF_5'), F_167)=k1_funct_1('#skF_5', k1_funct_1(D_168, F_167)) | k1_xboole_0=B_165 | ~r1_tarski(k2_relset_1(B_165, '#skF_3', D_168), k1_relat_1('#skF_5')) | ~m1_subset_1(F_167, B_165) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_168, k1_zfmisc_1(k2_zfmisc_1(B_165, '#skF_3'))) | ~v1_funct_2(D_168, B_165, '#skF_3') | ~v1_funct_1(D_168) | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_119, c_571])).
% 3.17/1.52  tff(c_585, plain, (![B_165, D_168, F_167]: (k1_funct_1(k8_funct_2(B_165, '#skF_3', '#skF_1', D_168, '#skF_5'), F_167)=k1_funct_1('#skF_5', k1_funct_1(D_168, F_167)) | k1_xboole_0=B_165 | ~r1_tarski(k2_relset_1(B_165, '#skF_3', D_168), k1_relat_1('#skF_5')) | ~m1_subset_1(F_167, B_165) | ~m1_subset_1(D_168, k1_zfmisc_1(k2_zfmisc_1(B_165, '#skF_3'))) | ~v1_funct_2(D_168, B_165, '#skF_3') | ~v1_funct_1(D_168) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_577])).
% 3.17/1.52  tff(c_597, plain, (![B_176, D_177, F_178]: (k1_funct_1(k8_funct_2(B_176, '#skF_3', '#skF_1', D_177, '#skF_5'), F_178)=k1_funct_1('#skF_5', k1_funct_1(D_177, F_178)) | k1_xboole_0=B_176 | ~r1_tarski(k2_relset_1(B_176, '#skF_3', D_177), k1_relat_1('#skF_5')) | ~m1_subset_1(F_178, B_176) | ~m1_subset_1(D_177, k1_zfmisc_1(k2_zfmisc_1(B_176, '#skF_3'))) | ~v1_funct_2(D_177, B_176, '#skF_3') | ~v1_funct_1(D_177))), inference(negUnitSimplification, [status(thm)], [c_62, c_585])).
% 3.17/1.52  tff(c_599, plain, (![F_178]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_178)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_178)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_178, '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_121, c_597])).
% 3.17/1.52  tff(c_602, plain, (![F_178]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_178)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_178)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_178, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_599])).
% 3.17/1.52  tff(c_604, plain, (![F_179]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_179)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_179)) | ~m1_subset_1(F_179, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_602])).
% 3.17/1.52  tff(c_84, plain, (![C_69, B_70, A_71]: (v5_relat_1(C_69, B_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.17/1.52  tff(c_91, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_84])).
% 3.17/1.52  tff(c_75, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.17/1.52  tff(c_82, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_75])).
% 3.17/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.17/1.52  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.17/1.52  tff(c_369, plain, (![D_123, C_124, B_125, A_126]: (r2_hidden(k1_funct_1(D_123, C_124), B_125) | k1_xboole_0=B_125 | ~r2_hidden(C_124, A_126) | ~m1_subset_1(D_123, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))) | ~v1_funct_2(D_123, A_126, B_125) | ~v1_funct_1(D_123))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.17/1.52  tff(c_381, plain, (![D_134, A_135, B_136, B_137]: (r2_hidden(k1_funct_1(D_134, A_135), B_136) | k1_xboole_0=B_136 | ~m1_subset_1(D_134, k1_zfmisc_1(k2_zfmisc_1(B_137, B_136))) | ~v1_funct_2(D_134, B_137, B_136) | ~v1_funct_1(D_134) | v1_xboole_0(B_137) | ~m1_subset_1(A_135, B_137))), inference(resolution, [status(thm)], [c_6, c_369])).
% 3.17/1.52  tff(c_385, plain, (![A_135]: (r2_hidden(k1_funct_1('#skF_4', A_135), '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_135, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_381])).
% 3.17/1.52  tff(c_392, plain, (![A_135]: (r2_hidden(k1_funct_1('#skF_4', A_135), '#skF_3') | k1_xboole_0='#skF_3' | v1_xboole_0('#skF_2') | ~m1_subset_1(A_135, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_385])).
% 3.17/1.52  tff(c_393, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_392])).
% 3.17/1.52  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.17/1.52  tff(c_396, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_393, c_4])).
% 3.17/1.52  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_396])).
% 3.17/1.52  tff(c_405, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_392])).
% 3.17/1.52  tff(c_373, plain, (![B_127, D_128, A_129, C_130]: (k1_xboole_0=B_127 | v1_funct_2(D_128, A_129, C_130) | ~r1_tarski(k2_relset_1(A_129, B_127, D_128), C_130) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_127))) | ~v1_funct_2(D_128, A_129, B_127) | ~v1_funct_1(D_128))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.17/1.52  tff(c_375, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_121, c_373])).
% 3.17/1.52  tff(c_378, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_375])).
% 3.17/1.52  tff(c_379, plain, (v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_378])).
% 3.17/1.52  tff(c_406, plain, (![B_138, D_139, A_140, C_141]: (k1_xboole_0=B_138 | m1_subset_1(D_139, k1_zfmisc_1(k2_zfmisc_1(A_140, C_141))) | ~r1_tarski(k2_relset_1(A_140, B_138, D_139), C_141) | ~m1_subset_1(D_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_138))) | ~v1_funct_2(D_139, A_140, B_138) | ~v1_funct_1(D_139))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.17/1.52  tff(c_408, plain, (k1_xboole_0='#skF_3' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_121, c_406])).
% 3.17/1.52  tff(c_411, plain, (k1_xboole_0='#skF_3' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_408])).
% 3.17/1.52  tff(c_412, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_5'))))), inference(splitLeft, [status(thm)], [c_411])).
% 3.17/1.52  tff(c_372, plain, (![D_123, A_2, B_125, B_3]: (r2_hidden(k1_funct_1(D_123, A_2), B_125) | k1_xboole_0=B_125 | ~m1_subset_1(D_123, k1_zfmisc_1(k2_zfmisc_1(B_3, B_125))) | ~v1_funct_2(D_123, B_3, B_125) | ~v1_funct_1(D_123) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(resolution, [status(thm)], [c_6, c_369])).
% 3.17/1.52  tff(c_414, plain, (![A_2]: (r2_hidden(k1_funct_1('#skF_4', A_2), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_2, '#skF_2'))), inference(resolution, [status(thm)], [c_412, c_372])).
% 3.17/1.52  tff(c_435, plain, (![A_2]: (r2_hidden(k1_funct_1('#skF_4', A_2), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_2') | ~m1_subset_1(A_2, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_379, c_414])).
% 3.17/1.52  tff(c_436, plain, (![A_2]: (r2_hidden(k1_funct_1('#skF_4', A_2), k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0 | ~m1_subset_1(A_2, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_405, c_435])).
% 3.17/1.52  tff(c_481, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_436])).
% 3.17/1.52  tff(c_130, plain, (![C_81, A_82, B_83]: (~v1_xboole_0(C_81) | ~v1_funct_2(C_81, A_82, B_83) | ~v1_funct_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | v1_xboole_0(B_83) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.17/1.52  tff(c_136, plain, (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_130])).
% 3.17/1.52  tff(c_143, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_136])).
% 3.17/1.52  tff(c_144, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_143])).
% 3.17/1.52  tff(c_145, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_144])).
% 3.17/1.52  tff(c_227, plain, (![D_97, C_98, B_99, A_100]: (r2_hidden(k1_funct_1(D_97, C_98), B_99) | k1_xboole_0=B_99 | ~r2_hidden(C_98, A_100) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))) | ~v1_funct_2(D_97, A_100, B_99) | ~v1_funct_1(D_97))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.17/1.52  tff(c_239, plain, (![D_108, A_109, B_110, B_111]: (r2_hidden(k1_funct_1(D_108, A_109), B_110) | k1_xboole_0=B_110 | ~m1_subset_1(D_108, k1_zfmisc_1(k2_zfmisc_1(B_111, B_110))) | ~v1_funct_2(D_108, B_111, B_110) | ~v1_funct_1(D_108) | v1_xboole_0(B_111) | ~m1_subset_1(A_109, B_111))), inference(resolution, [status(thm)], [c_6, c_227])).
% 3.17/1.52  tff(c_243, plain, (![A_109]: (r2_hidden(k1_funct_1('#skF_4', A_109), '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_109, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_239])).
% 3.17/1.52  tff(c_250, plain, (![A_109]: (r2_hidden(k1_funct_1('#skF_4', A_109), '#skF_3') | k1_xboole_0='#skF_3' | v1_xboole_0('#skF_2') | ~m1_subset_1(A_109, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_243])).
% 3.17/1.52  tff(c_251, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_250])).
% 3.17/1.52  tff(c_254, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_251, c_4])).
% 3.17/1.52  tff(c_261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_254])).
% 3.17/1.52  tff(c_262, plain, (![A_109]: (k1_xboole_0='#skF_3' | r2_hidden(k1_funct_1('#skF_4', A_109), '#skF_3') | ~m1_subset_1(A_109, '#skF_2'))), inference(splitRight, [status(thm)], [c_250])).
% 3.17/1.52  tff(c_264, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_262])).
% 3.17/1.52  tff(c_280, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_2])).
% 3.17/1.52  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_280])).
% 3.17/1.52  tff(c_286, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_262])).
% 3.17/1.52  tff(c_147, plain, (![A_84, B_85, C_86]: (k7_partfun1(A_84, B_85, C_86)=k1_funct_1(B_85, C_86) | ~r2_hidden(C_86, k1_relat_1(B_85)) | ~v1_funct_1(B_85) | ~v5_relat_1(B_85, A_84) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.17/1.52  tff(c_152, plain, (![A_87, B_88, A_89]: (k7_partfun1(A_87, B_88, A_89)=k1_funct_1(B_88, A_89) | ~v1_funct_1(B_88) | ~v5_relat_1(B_88, A_87) | ~v1_relat_1(B_88) | v1_xboole_0(k1_relat_1(B_88)) | ~m1_subset_1(A_89, k1_relat_1(B_88)))), inference(resolution, [status(thm)], [c_6, c_147])).
% 3.17/1.52  tff(c_154, plain, (![A_89]: (k7_partfun1('#skF_1', '#skF_5', A_89)=k1_funct_1('#skF_5', A_89) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_89, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_91, c_152])).
% 3.17/1.52  tff(c_159, plain, (![A_89]: (k7_partfun1('#skF_1', '#skF_5', A_89)=k1_funct_1('#skF_5', A_89) | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_89, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_54, c_154])).
% 3.17/1.52  tff(c_163, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_159])).
% 3.17/1.52  tff(c_171, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_163, c_4])).
% 3.17/1.52  tff(c_182, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_121])).
% 3.17/1.52  tff(c_291, plain, (![B_113, D_114, A_115, C_116]: (k1_xboole_0=B_113 | m1_subset_1(D_114, k1_zfmisc_1(k2_zfmisc_1(A_115, C_116))) | ~r1_tarski(k2_relset_1(A_115, B_113, D_114), C_116) | ~m1_subset_1(D_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_113))) | ~v1_funct_2(D_114, A_115, B_113) | ~v1_funct_1(D_114))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.17/1.52  tff(c_293, plain, (k1_xboole_0='#skF_3' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_xboole_0))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_182, c_291])).
% 3.17/1.52  tff(c_296, plain, (k1_xboole_0='#skF_3' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_293])).
% 3.17/1.52  tff(c_297, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_286, c_296])).
% 3.17/1.52  tff(c_16, plain, (![C_14, B_12, A_11]: (v1_xboole_0(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(B_12, A_11))) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.17/1.52  tff(c_308, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_297, c_16])).
% 3.17/1.52  tff(c_331, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_308])).
% 3.17/1.52  tff(c_333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_331])).
% 3.17/1.52  tff(c_335, plain, (~v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_159])).
% 3.17/1.52  tff(c_503, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_481, c_335])).
% 3.17/1.52  tff(c_508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_503])).
% 3.17/1.52  tff(c_511, plain, (![A_149]: (r2_hidden(k1_funct_1('#skF_4', A_149), k1_relat_1('#skF_5')) | ~m1_subset_1(A_149, '#skF_2'))), inference(splitRight, [status(thm)], [c_436])).
% 3.17/1.52  tff(c_26, plain, (![A_22, B_23, C_25]: (k7_partfun1(A_22, B_23, C_25)=k1_funct_1(B_23, C_25) | ~r2_hidden(C_25, k1_relat_1(B_23)) | ~v1_funct_1(B_23) | ~v5_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.17/1.52  tff(c_515, plain, (![A_22, A_149]: (k7_partfun1(A_22, '#skF_5', k1_funct_1('#skF_4', A_149))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_149)) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_22) | ~v1_relat_1('#skF_5') | ~m1_subset_1(A_149, '#skF_2'))), inference(resolution, [status(thm)], [c_511, c_26])).
% 3.17/1.52  tff(c_533, plain, (![A_153, A_154]: (k7_partfun1(A_153, '#skF_5', k1_funct_1('#skF_4', A_154))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_154)) | ~v5_relat_1('#skF_5', A_153) | ~m1_subset_1(A_154, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_54, c_515])).
% 3.17/1.52  tff(c_44, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.17/1.52  tff(c_539, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v5_relat_1('#skF_5', '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_533, c_44])).
% 3.17/1.52  tff(c_545, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_91, c_539])).
% 3.17/1.52  tff(c_618, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_604, c_545])).
% 3.17/1.52  tff(c_630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_618])).
% 3.17/1.52  tff(c_631, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_411])).
% 3.17/1.52  tff(c_644, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_631, c_2])).
% 3.17/1.52  tff(c_647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_644])).
% 3.17/1.52  tff(c_648, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_378])).
% 3.17/1.52  tff(c_658, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_648, c_2])).
% 3.17/1.52  tff(c_661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_658])).
% 3.17/1.52  tff(c_662, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_144])).
% 3.17/1.52  tff(c_666, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_662, c_4])).
% 3.17/1.52  tff(c_673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_666])).
% 3.17/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.52  
% 3.17/1.52  Inference rules
% 3.17/1.52  ----------------------
% 3.17/1.52  #Ref     : 0
% 3.17/1.52  #Sup     : 107
% 3.17/1.52  #Fact    : 0
% 3.17/1.52  #Define  : 0
% 3.17/1.52  #Split   : 14
% 3.17/1.52  #Chain   : 0
% 3.17/1.52  #Close   : 0
% 3.17/1.52  
% 3.17/1.52  Ordering : KBO
% 3.17/1.52  
% 3.17/1.52  Simplification rules
% 3.17/1.52  ----------------------
% 3.17/1.52  #Subsume      : 7
% 3.17/1.52  #Demod        : 181
% 3.17/1.52  #Tautology    : 41
% 3.17/1.52  #SimpNegUnit  : 28
% 3.17/1.52  #BackRed      : 69
% 3.17/1.52  
% 3.17/1.52  #Partial instantiations: 0
% 3.17/1.52  #Strategies tried      : 1
% 3.17/1.52  
% 3.17/1.52  Timing (in seconds)
% 3.17/1.52  ----------------------
% 3.17/1.52  Preprocessing        : 0.35
% 3.17/1.52  Parsing              : 0.18
% 3.17/1.52  CNF conversion       : 0.03
% 3.17/1.52  Main loop            : 0.35
% 3.17/1.52  Inferencing          : 0.11
% 3.17/1.52  Reduction            : 0.12
% 3.17/1.52  Demodulation         : 0.08
% 3.17/1.52  BG Simplification    : 0.02
% 3.17/1.52  Subsumption          : 0.07
% 3.17/1.52  Abstraction          : 0.02
% 3.17/1.52  MUC search           : 0.00
% 3.17/1.52  Cooper               : 0.00
% 3.17/1.52  Total                : 0.75
% 3.17/1.52  Index Insertion      : 0.00
% 3.17/1.52  Index Deletion       : 0.00
% 3.17/1.52  Index Matching       : 0.00
% 3.17/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
