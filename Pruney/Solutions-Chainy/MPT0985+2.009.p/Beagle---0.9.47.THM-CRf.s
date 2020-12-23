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
% DateTime   : Thu Dec  3 10:12:26 EST 2020

% Result     : Theorem 5.98s
% Output     : CNFRefutation 6.24s
% Verified   : 
% Statistics : Number of formulae       :  222 (2010 expanded)
%              Number of leaves         :   48 ( 697 expanded)
%              Depth                    :   18
%              Number of atoms          :  408 (5772 expanded)
%              Number of equality atoms :  123 (1172 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_205,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_160,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_143,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_133,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_156,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_178,axiom,(
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

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_188,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_148,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_58,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_92,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_2484,plain,(
    ! [C_223,A_224,B_225] :
      ( v1_relat_1(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2500,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_2484])).

tff(c_96,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_90,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_88,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_3639,plain,(
    ! [A_294,B_295,C_296] :
      ( k2_relset_1(A_294,B_295,C_296) = k2_relat_1(C_296)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_3652,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_3639])).

tff(c_3667,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3652])).

tff(c_58,plain,(
    ! [A_32] :
      ( k1_relat_1(k2_funct_1(A_32)) = k2_relat_1(A_32)
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_174,plain,(
    ! [A_67] :
      ( v1_funct_1(k2_funct_1(A_67))
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_86,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_156,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_177,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_174,c_156])).

tff(c_180,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_177])).

tff(c_305,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_308,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_305])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_308])).

tff(c_321,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_358,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_321])).

tff(c_445,plain,(
    ! [C_93,A_94,B_95] :
      ( v1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_457,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_445])).

tff(c_754,plain,(
    ! [A_135,B_136,C_137] :
      ( k2_relset_1(A_135,B_136,C_137) = k2_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_757,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_754])).

tff(c_769,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_757])).

tff(c_50,plain,(
    ! [A_26] :
      ( v1_relat_1(k2_funct_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_322,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    ! [A_22] :
      ( k10_relat_1(A_22,k2_relat_1(A_22)) = k1_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_778,plain,
    ( k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_36])).

tff(c_784,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_778])).

tff(c_986,plain,(
    ! [B_153,A_154] :
      ( k9_relat_1(B_153,k10_relat_1(B_153,A_154)) = A_154
      | ~ r1_tarski(A_154,k2_relat_1(B_153))
      | ~ v1_funct_1(B_153)
      | ~ v1_relat_1(B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_988,plain,(
    ! [A_154] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_154)) = A_154
      | ~ r1_tarski(A_154,'#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_986])).

tff(c_1005,plain,(
    ! [A_155] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_155)) = A_155
      | ~ r1_tarski(A_155,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_96,c_988])).

tff(c_1014,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_1005])).

tff(c_1022,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1014])).

tff(c_1075,plain,(
    ! [A_158,B_159] :
      ( k9_relat_1(k2_funct_1(A_158),k9_relat_1(A_158,B_159)) = B_159
      | ~ r1_tarski(B_159,k1_relat_1(A_158))
      | ~ v2_funct_1(A_158)
      | ~ v1_funct_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1093,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1022,c_1075])).

tff(c_1106,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_96,c_90,c_12,c_1093])).

tff(c_54,plain,(
    ! [A_29,B_31] :
      ( k9_relat_1(k2_funct_1(A_29),k9_relat_1(A_29,B_31)) = B_31
      | ~ r1_tarski(B_31,k1_relat_1(A_29))
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1116,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1106,c_54])).

tff(c_1120,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_1116])).

tff(c_1328,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1120])).

tff(c_1331,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1328])).

tff(c_1335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_96,c_1331])).

tff(c_1337,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1120])).

tff(c_94,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_683,plain,(
    ! [A_120,B_121,C_122] :
      ( k1_relset_1(A_120,B_121,C_122) = k1_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_697,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_683])).

tff(c_1364,plain,(
    ! [B_176,A_177,C_178] :
      ( k1_xboole_0 = B_176
      | k1_relset_1(A_177,B_176,C_178) = A_177
      | ~ v1_funct_2(C_178,A_177,B_176)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_177,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1373,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_1364])).

tff(c_1390,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_697,c_1373])).

tff(c_1394,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1390])).

tff(c_34,plain,(
    ! [A_21] :
      ( k9_relat_1(A_21,k1_relat_1(A_21)) = k2_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1430,plain,
    ( k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1394,c_34])).

tff(c_1447,plain,(
    k9_relat_1('#skF_4','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_769,c_1430])).

tff(c_1465,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1447,c_54])).

tff(c_1469,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_96,c_90,c_12,c_1394,c_1465])).

tff(c_536,plain,(
    ! [A_112] :
      ( k1_relat_1(k2_funct_1(A_112)) = k2_relat_1(A_112)
      | ~ v2_funct_1(A_112)
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1648,plain,(
    ! [A_187] :
      ( k9_relat_1(k2_funct_1(A_187),k2_relat_1(A_187)) = k2_relat_1(k2_funct_1(A_187))
      | ~ v1_relat_1(k2_funct_1(A_187))
      | ~ v2_funct_1(A_187)
      | ~ v1_funct_1(A_187)
      | ~ v1_relat_1(A_187) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_34])).

tff(c_1669,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_1648])).

tff(c_1682,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_96,c_90,c_1337,c_1469,c_1669])).

tff(c_80,plain,(
    ! [A_47] :
      ( m1_subset_1(A_47,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_47),k2_relat_1(A_47))))
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1713,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1682,c_80])).

tff(c_1745,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_322,c_1713])).

tff(c_1963,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),'#skF_2')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1745])).

tff(c_1978,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_96,c_90,c_769,c_1963])).

tff(c_1980,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_1978])).

tff(c_1981,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1390])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_325,plain,(
    ! [A_84] :
      ( v1_xboole_0(A_84)
      | r2_hidden('#skF_1'(A_84),A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [B_34,A_33] :
      ( ~ r1_tarski(B_34,A_33)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_334,plain,(
    ! [A_85] :
      ( ~ r1_tarski(A_85,'#skF_1'(A_85))
      | v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_325,c_60])).

tff(c_339,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_334])).

tff(c_2017,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1981,c_339])).

tff(c_18,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2021,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1981,c_1981,c_18])).

tff(c_489,plain,(
    ! [A_102] :
      ( k4_relat_1(A_102) = k2_funct_1(A_102)
      | ~ v2_funct_1(A_102)
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_495,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_489])).

tff(c_499,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_96,c_495])).

tff(c_30,plain,(
    ! [A_20] :
      ( v1_relat_1(k4_relat_1(A_20))
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_509,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_30])).

tff(c_517,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_509])).

tff(c_803,plain,(
    ! [A_142] :
      ( m1_subset_1(A_142,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_142),k2_relat_1(A_142))))
      | ~ v1_funct_1(A_142)
      | ~ v1_relat_1(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_820,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_803])).

tff(c_836,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_96,c_820])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_532,plain,(
    ! [C_109,A_110,B_111] :
      ( r2_hidden(C_109,A_110)
      | ~ r2_hidden(C_109,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_655,plain,(
    ! [A_116,A_117] :
      ( r2_hidden('#skF_1'(A_116),A_117)
      | ~ m1_subset_1(A_116,k1_zfmisc_1(A_117))
      | v1_xboole_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_4,c_532])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_670,plain,(
    ! [A_117,A_116] :
      ( ~ v1_xboole_0(A_117)
      | ~ m1_subset_1(A_116,k1_zfmisc_1(A_117))
      | v1_xboole_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_655,c_2])).

tff(c_847,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_836,c_670])).

tff(c_858,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_517,c_847])).

tff(c_2181,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2021,c_858])).

tff(c_2192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2017,c_2181])).

tff(c_2194,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_509])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2208,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2194,c_6])).

tff(c_24,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2226,plain,(
    ! [A_15] : m1_subset_1('#skF_4',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2208,c_24])).

tff(c_131,plain,(
    ! [A_56] :
      ( v1_xboole_0(k4_relat_1(A_56))
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_141,plain,(
    ! [A_56] :
      ( k4_relat_1(A_56) = k1_xboole_0
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_131,c_6])).

tff(c_2207,plain,(
    k4_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2194,c_141])).

tff(c_2239,plain,(
    k4_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2208,c_2207])).

tff(c_2240,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2239,c_499])).

tff(c_2272,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2240,c_358])).

tff(c_2374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2226,c_2272])).

tff(c_2375,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_2376,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_3773,plain,(
    ! [A_309,B_310,C_311] :
      ( k1_relset_1(A_309,B_310,C_311) = k1_relat_1(C_311)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_3798,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2376,c_3773])).

tff(c_4087,plain,(
    ! [B_331,C_332,A_333] :
      ( k1_xboole_0 = B_331
      | v1_funct_2(C_332,A_333,B_331)
      | k1_relset_1(A_333,B_331,C_332) != A_333
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_333,B_331))) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_4096,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_2376,c_4087])).

tff(c_4115,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3798,c_4096])).

tff(c_4116,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2375,c_4115])).

tff(c_4122,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4116])).

tff(c_4125,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_4122])).

tff(c_4128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2500,c_96,c_90,c_3667,c_4125])).

tff(c_4129,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4116])).

tff(c_4160,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4129,c_339])).

tff(c_20,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4163,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_2',B_10) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4129,c_4129,c_20])).

tff(c_2514,plain,(
    ! [A_230] :
      ( k4_relat_1(A_230) = k2_funct_1(A_230)
      | ~ v2_funct_1(A_230)
      | ~ v1_funct_1(A_230)
      | ~ v1_relat_1(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2520,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_2514])).

tff(c_2524,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2500,c_96,c_2520])).

tff(c_32,plain,(
    ! [A_20] :
      ( v1_xboole_0(k4_relat_1(A_20))
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2537,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2524,c_32])).

tff(c_2543,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2537])).

tff(c_2510,plain,(
    ! [C_227,A_228,B_229] :
      ( r2_hidden(C_227,A_228)
      | ~ r2_hidden(C_227,B_229)
      | ~ m1_subset_1(B_229,k1_zfmisc_1(A_228)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2568,plain,(
    ! [A_239,A_240] :
      ( r2_hidden('#skF_1'(A_239),A_240)
      | ~ m1_subset_1(A_239,k1_zfmisc_1(A_240))
      | v1_xboole_0(A_239) ) ),
    inference(resolution,[status(thm)],[c_4,c_2510])).

tff(c_2589,plain,(
    ! [A_241,A_242] :
      ( ~ v1_xboole_0(A_241)
      | ~ m1_subset_1(A_242,k1_zfmisc_1(A_241))
      | v1_xboole_0(A_242) ) ),
    inference(resolution,[status(thm)],[c_2568,c_2])).

tff(c_2595,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_2589])).

tff(c_2602,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_2543,c_2595])).

tff(c_4352,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4163,c_2602])).

tff(c_4357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4160,c_4352])).

tff(c_4359,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2537])).

tff(c_4373,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4359,c_6])).

tff(c_4372,plain,(
    k4_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4359,c_141])).

tff(c_4433,plain,(
    k4_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_4372])).

tff(c_4434,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4433,c_2524])).

tff(c_4610,plain,(
    ! [A_355] :
      ( k1_relat_1(k2_funct_1(A_355)) = k2_relat_1(A_355)
      | ~ v2_funct_1(A_355)
      | ~ v1_funct_1(A_355)
      | ~ v1_relat_1(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4625,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4434,c_4610])).

tff(c_4629,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2500,c_96,c_90,c_4625])).

tff(c_4414,plain,(
    ! [A_15] : m1_subset_1('#skF_4',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_24])).

tff(c_4810,plain,(
    ! [A_382,B_383,C_384] :
      ( k2_relset_1(A_382,B_383,C_384) = k2_relat_1(C_384)
      | ~ m1_subset_1(C_384,k1_zfmisc_1(k2_zfmisc_1(A_382,B_383))) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_4820,plain,(
    ! [A_382,B_383] : k2_relset_1(A_382,B_383,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4414,c_4810])).

tff(c_4827,plain,(
    ! [A_385,B_386] : k2_relset_1(A_385,B_386,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4629,c_4820])).

tff(c_4831,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4827,c_88])).

tff(c_82,plain,(
    ! [A_47] :
      ( v1_funct_2(A_47,k1_relat_1(A_47),k2_relat_1(A_47))
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_4633,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4629,c_82])).

tff(c_4640,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2500,c_96,c_4633])).

tff(c_4841,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4831,c_4831,c_4640])).

tff(c_4737,plain,(
    ! [A_369,B_370,C_371] :
      ( k1_relset_1(A_369,B_370,C_371) = k1_relat_1(C_371)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_369,B_370))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_4748,plain,(
    ! [A_369,B_370] : k1_relset_1(A_369,B_370,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4414,c_4737])).

tff(c_4839,plain,(
    ! [A_369,B_370] : k1_relset_1(A_369,B_370,'#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4831,c_4748])).

tff(c_72,plain,(
    ! [C_46,B_45] :
      ( v1_funct_2(C_46,k1_xboole_0,B_45)
      | k1_relset_1(k1_xboole_0,B_45,C_46) != k1_xboole_0
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_100,plain,(
    ! [C_46,B_45] :
      ( v1_funct_2(C_46,k1_xboole_0,B_45)
      | k1_relset_1(k1_xboole_0,B_45,C_46) != k1_xboole_0
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_72])).

tff(c_4888,plain,(
    ! [C_387,B_388] :
      ( v1_funct_2(C_387,'#skF_4',B_388)
      | k1_relset_1('#skF_4',B_388,C_387) != '#skF_4'
      | ~ m1_subset_1(C_387,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_4373,c_4373,c_4373,c_100])).

tff(c_4892,plain,(
    ! [B_388] :
      ( v1_funct_2('#skF_4','#skF_4',B_388)
      | k1_relset_1('#skF_4',B_388,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_4414,c_4888])).

tff(c_4915,plain,(
    ! [B_388] :
      ( v1_funct_2('#skF_4','#skF_4',B_388)
      | '#skF_3' != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4839,c_4892])).

tff(c_4916,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4915])).

tff(c_78,plain,(
    ! [B_45,A_44,C_46] :
      ( k1_xboole_0 = B_45
      | k1_relset_1(A_44,B_45,C_46) = A_44
      | ~ v1_funct_2(C_46,A_44,B_45)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_5153,plain,(
    ! [B_410,A_411,C_412] :
      ( B_410 = '#skF_4'
      | k1_relset_1(A_411,B_410,C_412) = A_411
      | ~ v1_funct_2(C_412,A_411,B_410)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(A_411,B_410))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_78])).

tff(c_5163,plain,(
    ! [B_410,A_411] :
      ( B_410 = '#skF_4'
      | k1_relset_1(A_411,B_410,'#skF_4') = A_411
      | ~ v1_funct_2('#skF_4',A_411,B_410) ) ),
    inference(resolution,[status(thm)],[c_4414,c_5153])).

tff(c_5171,plain,(
    ! [B_413,A_414] :
      ( B_413 = '#skF_4'
      | A_414 = '#skF_3'
      | ~ v1_funct_2('#skF_4',A_414,B_413) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4839,c_5163])).

tff(c_5184,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_94,c_5171])).

tff(c_5197,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4916,c_5184])).

tff(c_4475,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4434,c_2375])).

tff(c_5198,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5197,c_4475])).

tff(c_5202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4841,c_5198])).

tff(c_5203,plain,(
    ! [B_388] : v1_funct_2('#skF_4','#skF_4',B_388) ),
    inference(splitRight,[status(thm)],[c_4915])).

tff(c_5204,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4915])).

tff(c_5212,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5204,c_4475])).

tff(c_5296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5203,c_5212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.98/2.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.19  
% 5.98/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.19  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 5.98/2.19  
% 5.98/2.19  %Foreground sorts:
% 5.98/2.19  
% 5.98/2.19  
% 5.98/2.19  %Background operators:
% 5.98/2.19  
% 5.98/2.19  
% 5.98/2.19  %Foreground operators:
% 5.98/2.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.98/2.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.98/2.19  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.98/2.19  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.98/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.98/2.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.98/2.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.98/2.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.98/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.98/2.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.98/2.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.98/2.19  tff('#skF_2', type, '#skF_2': $i).
% 5.98/2.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.98/2.19  tff('#skF_3', type, '#skF_3': $i).
% 5.98/2.19  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.98/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.98/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.98/2.19  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.98/2.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.98/2.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.98/2.19  tff('#skF_4', type, '#skF_4': $i).
% 5.98/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.98/2.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.98/2.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.98/2.19  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.98/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.98/2.19  
% 6.24/2.23  tff(f_205, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 6.24/2.23  tff(f_152, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.24/2.23  tff(f_160, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.24/2.23  tff(f_143, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.24/2.23  tff(f_114, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.24/2.23  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.24/2.23  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 6.24/2.23  tff(f_122, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 6.24/2.23  tff(f_133, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 6.24/2.23  tff(f_156, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.24/2.23  tff(f_178, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.24/2.23  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 6.24/2.23  tff(f_188, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 6.24/2.23  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.24/2.23  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.24/2.23  tff(f_148, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.24/2.23  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.24/2.23  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 6.24/2.23  tff(f_74, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 6.24/2.23  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 6.24/2.23  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.24/2.23  tff(f_58, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.24/2.23  tff(c_92, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 6.24/2.23  tff(c_2484, plain, (![C_223, A_224, B_225]: (v1_relat_1(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.24/2.23  tff(c_2500, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_2484])).
% 6.24/2.23  tff(c_96, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 6.24/2.23  tff(c_90, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 6.24/2.23  tff(c_88, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_205])).
% 6.24/2.23  tff(c_3639, plain, (![A_294, B_295, C_296]: (k2_relset_1(A_294, B_295, C_296)=k2_relat_1(C_296) | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.24/2.23  tff(c_3652, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_3639])).
% 6.24/2.23  tff(c_3667, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3652])).
% 6.24/2.23  tff(c_58, plain, (![A_32]: (k1_relat_1(k2_funct_1(A_32))=k2_relat_1(A_32) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.24/2.23  tff(c_174, plain, (![A_67]: (v1_funct_1(k2_funct_1(A_67)) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.24/2.23  tff(c_86, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 6.24/2.23  tff(c_156, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_86])).
% 6.24/2.23  tff(c_177, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_174, c_156])).
% 6.24/2.23  tff(c_180, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_177])).
% 6.24/2.23  tff(c_305, plain, (![C_78, A_79, B_80]: (v1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.24/2.23  tff(c_308, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_305])).
% 6.24/2.23  tff(c_320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_308])).
% 6.24/2.23  tff(c_321, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_86])).
% 6.24/2.23  tff(c_358, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_321])).
% 6.24/2.23  tff(c_445, plain, (![C_93, A_94, B_95]: (v1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.24/2.23  tff(c_457, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_445])).
% 6.24/2.23  tff(c_754, plain, (![A_135, B_136, C_137]: (k2_relset_1(A_135, B_136, C_137)=k2_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.24/2.23  tff(c_757, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_754])).
% 6.24/2.23  tff(c_769, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_757])).
% 6.24/2.23  tff(c_50, plain, (![A_26]: (v1_relat_1(k2_funct_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.24/2.23  tff(c_322, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_86])).
% 6.24/2.23  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.24/2.23  tff(c_36, plain, (![A_22]: (k10_relat_1(A_22, k2_relat_1(A_22))=k1_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.24/2.23  tff(c_778, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_769, c_36])).
% 6.24/2.23  tff(c_784, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_778])).
% 6.24/2.23  tff(c_986, plain, (![B_153, A_154]: (k9_relat_1(B_153, k10_relat_1(B_153, A_154))=A_154 | ~r1_tarski(A_154, k2_relat_1(B_153)) | ~v1_funct_1(B_153) | ~v1_relat_1(B_153))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.24/2.23  tff(c_988, plain, (![A_154]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_154))=A_154 | ~r1_tarski(A_154, '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_769, c_986])).
% 6.24/2.23  tff(c_1005, plain, (![A_155]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_155))=A_155 | ~r1_tarski(A_155, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_96, c_988])).
% 6.24/2.23  tff(c_1014, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_784, c_1005])).
% 6.24/2.23  tff(c_1022, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1014])).
% 6.24/2.23  tff(c_1075, plain, (![A_158, B_159]: (k9_relat_1(k2_funct_1(A_158), k9_relat_1(A_158, B_159))=B_159 | ~r1_tarski(B_159, k1_relat_1(A_158)) | ~v2_funct_1(A_158) | ~v1_funct_1(A_158) | ~v1_relat_1(A_158))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.24/2.23  tff(c_1093, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1022, c_1075])).
% 6.24/2.23  tff(c_1106, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_96, c_90, c_12, c_1093])).
% 6.24/2.23  tff(c_54, plain, (![A_29, B_31]: (k9_relat_1(k2_funct_1(A_29), k9_relat_1(A_29, B_31))=B_31 | ~r1_tarski(B_31, k1_relat_1(A_29)) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.24/2.23  tff(c_1116, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1106, c_54])).
% 6.24/2.23  tff(c_1120, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_1116])).
% 6.24/2.23  tff(c_1328, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1120])).
% 6.24/2.23  tff(c_1331, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1328])).
% 6.24/2.23  tff(c_1335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_457, c_96, c_1331])).
% 6.24/2.23  tff(c_1337, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1120])).
% 6.24/2.23  tff(c_94, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 6.24/2.23  tff(c_683, plain, (![A_120, B_121, C_122]: (k1_relset_1(A_120, B_121, C_122)=k1_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.24/2.23  tff(c_697, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_683])).
% 6.24/2.23  tff(c_1364, plain, (![B_176, A_177, C_178]: (k1_xboole_0=B_176 | k1_relset_1(A_177, B_176, C_178)=A_177 | ~v1_funct_2(C_178, A_177, B_176) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_177, B_176))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.24/2.23  tff(c_1373, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_92, c_1364])).
% 6.24/2.23  tff(c_1390, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_697, c_1373])).
% 6.24/2.23  tff(c_1394, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1390])).
% 6.24/2.23  tff(c_34, plain, (![A_21]: (k9_relat_1(A_21, k1_relat_1(A_21))=k2_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.24/2.23  tff(c_1430, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1394, c_34])).
% 6.24/2.23  tff(c_1447, plain, (k9_relat_1('#skF_4', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_457, c_769, c_1430])).
% 6.24/2.23  tff(c_1465, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1447, c_54])).
% 6.24/2.23  tff(c_1469, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_457, c_96, c_90, c_12, c_1394, c_1465])).
% 6.24/2.23  tff(c_536, plain, (![A_112]: (k1_relat_1(k2_funct_1(A_112))=k2_relat_1(A_112) | ~v2_funct_1(A_112) | ~v1_funct_1(A_112) | ~v1_relat_1(A_112))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.24/2.23  tff(c_1648, plain, (![A_187]: (k9_relat_1(k2_funct_1(A_187), k2_relat_1(A_187))=k2_relat_1(k2_funct_1(A_187)) | ~v1_relat_1(k2_funct_1(A_187)) | ~v2_funct_1(A_187) | ~v1_funct_1(A_187) | ~v1_relat_1(A_187))), inference(superposition, [status(thm), theory('equality')], [c_536, c_34])).
% 6.24/2.23  tff(c_1669, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_769, c_1648])).
% 6.24/2.23  tff(c_1682, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_457, c_96, c_90, c_1337, c_1469, c_1669])).
% 6.24/2.23  tff(c_80, plain, (![A_47]: (m1_subset_1(A_47, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_47), k2_relat_1(A_47)))) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_188])).
% 6.24/2.23  tff(c_1713, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1682, c_80])).
% 6.24/2.23  tff(c_1745, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_322, c_1713])).
% 6.24/2.23  tff(c_1963, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), '#skF_2'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_58, c_1745])).
% 6.24/2.23  tff(c_1978, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_96, c_90, c_769, c_1963])).
% 6.24/2.23  tff(c_1980, plain, $false, inference(negUnitSimplification, [status(thm)], [c_358, c_1978])).
% 6.24/2.23  tff(c_1981, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1390])).
% 6.24/2.23  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.24/2.23  tff(c_325, plain, (![A_84]: (v1_xboole_0(A_84) | r2_hidden('#skF_1'(A_84), A_84))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.24/2.23  tff(c_60, plain, (![B_34, A_33]: (~r1_tarski(B_34, A_33) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.24/2.23  tff(c_334, plain, (![A_85]: (~r1_tarski(A_85, '#skF_1'(A_85)) | v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_325, c_60])).
% 6.24/2.23  tff(c_339, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_334])).
% 6.24/2.23  tff(c_2017, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1981, c_339])).
% 6.24/2.23  tff(c_18, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.24/2.23  tff(c_2021, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1981, c_1981, c_18])).
% 6.24/2.23  tff(c_489, plain, (![A_102]: (k4_relat_1(A_102)=k2_funct_1(A_102) | ~v2_funct_1(A_102) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.24/2.23  tff(c_495, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_489])).
% 6.24/2.23  tff(c_499, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_96, c_495])).
% 6.24/2.23  tff(c_30, plain, (![A_20]: (v1_relat_1(k4_relat_1(A_20)) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.24/2.23  tff(c_509, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_499, c_30])).
% 6.24/2.23  tff(c_517, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_509])).
% 6.24/2.23  tff(c_803, plain, (![A_142]: (m1_subset_1(A_142, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_142), k2_relat_1(A_142)))) | ~v1_funct_1(A_142) | ~v1_relat_1(A_142))), inference(cnfTransformation, [status(thm)], [f_188])).
% 6.24/2.23  tff(c_820, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_769, c_803])).
% 6.24/2.23  tff(c_836, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_96, c_820])).
% 6.24/2.23  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.24/2.23  tff(c_532, plain, (![C_109, A_110, B_111]: (r2_hidden(C_109, A_110) | ~r2_hidden(C_109, B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.24/2.23  tff(c_655, plain, (![A_116, A_117]: (r2_hidden('#skF_1'(A_116), A_117) | ~m1_subset_1(A_116, k1_zfmisc_1(A_117)) | v1_xboole_0(A_116))), inference(resolution, [status(thm)], [c_4, c_532])).
% 6.24/2.23  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.24/2.23  tff(c_670, plain, (![A_117, A_116]: (~v1_xboole_0(A_117) | ~m1_subset_1(A_116, k1_zfmisc_1(A_117)) | v1_xboole_0(A_116))), inference(resolution, [status(thm)], [c_655, c_2])).
% 6.24/2.23  tff(c_847, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_836, c_670])).
% 6.24/2.23  tff(c_858, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_517, c_847])).
% 6.24/2.23  tff(c_2181, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2021, c_858])).
% 6.24/2.23  tff(c_2192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2017, c_2181])).
% 6.24/2.23  tff(c_2194, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_509])).
% 6.24/2.23  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.24/2.23  tff(c_2208, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2194, c_6])).
% 6.24/2.23  tff(c_24, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.24/2.23  tff(c_2226, plain, (![A_15]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_2208, c_24])).
% 6.24/2.23  tff(c_131, plain, (![A_56]: (v1_xboole_0(k4_relat_1(A_56)) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.24/2.23  tff(c_141, plain, (![A_56]: (k4_relat_1(A_56)=k1_xboole_0 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_131, c_6])).
% 6.24/2.23  tff(c_2207, plain, (k4_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2194, c_141])).
% 6.24/2.23  tff(c_2239, plain, (k4_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2208, c_2207])).
% 6.24/2.23  tff(c_2240, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2239, c_499])).
% 6.24/2.23  tff(c_2272, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2240, c_358])).
% 6.24/2.23  tff(c_2374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2226, c_2272])).
% 6.24/2.23  tff(c_2375, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_321])).
% 6.24/2.23  tff(c_2376, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_321])).
% 6.24/2.23  tff(c_3773, plain, (![A_309, B_310, C_311]: (k1_relset_1(A_309, B_310, C_311)=k1_relat_1(C_311) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.24/2.23  tff(c_3798, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2376, c_3773])).
% 6.24/2.23  tff(c_4087, plain, (![B_331, C_332, A_333]: (k1_xboole_0=B_331 | v1_funct_2(C_332, A_333, B_331) | k1_relset_1(A_333, B_331, C_332)!=A_333 | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_333, B_331))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.24/2.23  tff(c_4096, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_2376, c_4087])).
% 6.24/2.23  tff(c_4115, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3798, c_4096])).
% 6.24/2.23  tff(c_4116, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2375, c_4115])).
% 6.24/2.23  tff(c_4122, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_4116])).
% 6.24/2.23  tff(c_4125, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_58, c_4122])).
% 6.24/2.23  tff(c_4128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2500, c_96, c_90, c_3667, c_4125])).
% 6.24/2.23  tff(c_4129, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4116])).
% 6.24/2.23  tff(c_4160, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4129, c_339])).
% 6.24/2.23  tff(c_20, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.24/2.23  tff(c_4163, plain, (![B_10]: (k2_zfmisc_1('#skF_2', B_10)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4129, c_4129, c_20])).
% 6.24/2.23  tff(c_2514, plain, (![A_230]: (k4_relat_1(A_230)=k2_funct_1(A_230) | ~v2_funct_1(A_230) | ~v1_funct_1(A_230) | ~v1_relat_1(A_230))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.24/2.23  tff(c_2520, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_2514])).
% 6.24/2.23  tff(c_2524, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2500, c_96, c_2520])).
% 6.24/2.23  tff(c_32, plain, (![A_20]: (v1_xboole_0(k4_relat_1(A_20)) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.24/2.23  tff(c_2537, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2524, c_32])).
% 6.24/2.23  tff(c_2543, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_2537])).
% 6.24/2.23  tff(c_2510, plain, (![C_227, A_228, B_229]: (r2_hidden(C_227, A_228) | ~r2_hidden(C_227, B_229) | ~m1_subset_1(B_229, k1_zfmisc_1(A_228)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.24/2.23  tff(c_2568, plain, (![A_239, A_240]: (r2_hidden('#skF_1'(A_239), A_240) | ~m1_subset_1(A_239, k1_zfmisc_1(A_240)) | v1_xboole_0(A_239))), inference(resolution, [status(thm)], [c_4, c_2510])).
% 6.24/2.23  tff(c_2589, plain, (![A_241, A_242]: (~v1_xboole_0(A_241) | ~m1_subset_1(A_242, k1_zfmisc_1(A_241)) | v1_xboole_0(A_242))), inference(resolution, [status(thm)], [c_2568, c_2])).
% 6.24/2.23  tff(c_2595, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_92, c_2589])).
% 6.24/2.23  tff(c_2602, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2543, c_2595])).
% 6.24/2.23  tff(c_4352, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4163, c_2602])).
% 6.24/2.23  tff(c_4357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4160, c_4352])).
% 6.24/2.23  tff(c_4359, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_2537])).
% 6.24/2.23  tff(c_4373, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4359, c_6])).
% 6.24/2.23  tff(c_4372, plain, (k4_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_4359, c_141])).
% 6.24/2.23  tff(c_4433, plain, (k4_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4373, c_4372])).
% 6.24/2.23  tff(c_4434, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4433, c_2524])).
% 6.24/2.23  tff(c_4610, plain, (![A_355]: (k1_relat_1(k2_funct_1(A_355))=k2_relat_1(A_355) | ~v2_funct_1(A_355) | ~v1_funct_1(A_355) | ~v1_relat_1(A_355))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.24/2.23  tff(c_4625, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4434, c_4610])).
% 6.24/2.23  tff(c_4629, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2500, c_96, c_90, c_4625])).
% 6.24/2.23  tff(c_4414, plain, (![A_15]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_4373, c_24])).
% 6.24/2.23  tff(c_4810, plain, (![A_382, B_383, C_384]: (k2_relset_1(A_382, B_383, C_384)=k2_relat_1(C_384) | ~m1_subset_1(C_384, k1_zfmisc_1(k2_zfmisc_1(A_382, B_383))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.24/2.23  tff(c_4820, plain, (![A_382, B_383]: (k2_relset_1(A_382, B_383, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4414, c_4810])).
% 6.24/2.23  tff(c_4827, plain, (![A_385, B_386]: (k2_relset_1(A_385, B_386, '#skF_4')=k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4629, c_4820])).
% 6.24/2.23  tff(c_4831, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4827, c_88])).
% 6.24/2.23  tff(c_82, plain, (![A_47]: (v1_funct_2(A_47, k1_relat_1(A_47), k2_relat_1(A_47)) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_188])).
% 6.24/2.23  tff(c_4633, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4629, c_82])).
% 6.24/2.23  tff(c_4640, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2500, c_96, c_4633])).
% 6.24/2.23  tff(c_4841, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4831, c_4831, c_4640])).
% 6.24/2.23  tff(c_4737, plain, (![A_369, B_370, C_371]: (k1_relset_1(A_369, B_370, C_371)=k1_relat_1(C_371) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_369, B_370))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.24/2.23  tff(c_4748, plain, (![A_369, B_370]: (k1_relset_1(A_369, B_370, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4414, c_4737])).
% 6.24/2.23  tff(c_4839, plain, (![A_369, B_370]: (k1_relset_1(A_369, B_370, '#skF_4')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4831, c_4748])).
% 6.24/2.23  tff(c_72, plain, (![C_46, B_45]: (v1_funct_2(C_46, k1_xboole_0, B_45) | k1_relset_1(k1_xboole_0, B_45, C_46)!=k1_xboole_0 | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_45))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.24/2.23  tff(c_100, plain, (![C_46, B_45]: (v1_funct_2(C_46, k1_xboole_0, B_45) | k1_relset_1(k1_xboole_0, B_45, C_46)!=k1_xboole_0 | ~m1_subset_1(C_46, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_72])).
% 6.24/2.23  tff(c_4888, plain, (![C_387, B_388]: (v1_funct_2(C_387, '#skF_4', B_388) | k1_relset_1('#skF_4', B_388, C_387)!='#skF_4' | ~m1_subset_1(C_387, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4373, c_4373, c_4373, c_4373, c_100])).
% 6.24/2.23  tff(c_4892, plain, (![B_388]: (v1_funct_2('#skF_4', '#skF_4', B_388) | k1_relset_1('#skF_4', B_388, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_4414, c_4888])).
% 6.24/2.23  tff(c_4915, plain, (![B_388]: (v1_funct_2('#skF_4', '#skF_4', B_388) | '#skF_3'!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4839, c_4892])).
% 6.24/2.23  tff(c_4916, plain, ('#skF_3'!='#skF_4'), inference(splitLeft, [status(thm)], [c_4915])).
% 6.24/2.23  tff(c_78, plain, (![B_45, A_44, C_46]: (k1_xboole_0=B_45 | k1_relset_1(A_44, B_45, C_46)=A_44 | ~v1_funct_2(C_46, A_44, B_45) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.24/2.23  tff(c_5153, plain, (![B_410, A_411, C_412]: (B_410='#skF_4' | k1_relset_1(A_411, B_410, C_412)=A_411 | ~v1_funct_2(C_412, A_411, B_410) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(A_411, B_410))))), inference(demodulation, [status(thm), theory('equality')], [c_4373, c_78])).
% 6.24/2.23  tff(c_5163, plain, (![B_410, A_411]: (B_410='#skF_4' | k1_relset_1(A_411, B_410, '#skF_4')=A_411 | ~v1_funct_2('#skF_4', A_411, B_410))), inference(resolution, [status(thm)], [c_4414, c_5153])).
% 6.24/2.23  tff(c_5171, plain, (![B_413, A_414]: (B_413='#skF_4' | A_414='#skF_3' | ~v1_funct_2('#skF_4', A_414, B_413))), inference(demodulation, [status(thm), theory('equality')], [c_4839, c_5163])).
% 6.24/2.23  tff(c_5184, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_94, c_5171])).
% 6.24/2.23  tff(c_5197, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4916, c_5184])).
% 6.24/2.23  tff(c_4475, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4434, c_2375])).
% 6.24/2.23  tff(c_5198, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5197, c_4475])).
% 6.24/2.23  tff(c_5202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4841, c_5198])).
% 6.24/2.23  tff(c_5203, plain, (![B_388]: (v1_funct_2('#skF_4', '#skF_4', B_388))), inference(splitRight, [status(thm)], [c_4915])).
% 6.24/2.23  tff(c_5204, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_4915])).
% 6.24/2.23  tff(c_5212, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5204, c_4475])).
% 6.24/2.23  tff(c_5296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5203, c_5212])).
% 6.24/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.24/2.23  
% 6.24/2.23  Inference rules
% 6.24/2.23  ----------------------
% 6.24/2.23  #Ref     : 0
% 6.24/2.23  #Sup     : 1123
% 6.24/2.23  #Fact    : 0
% 6.24/2.23  #Define  : 0
% 6.24/2.23  #Split   : 21
% 6.24/2.23  #Chain   : 0
% 6.24/2.23  #Close   : 0
% 6.24/2.23  
% 6.24/2.23  Ordering : KBO
% 6.24/2.23  
% 6.24/2.23  Simplification rules
% 6.24/2.23  ----------------------
% 6.24/2.23  #Subsume      : 77
% 6.24/2.23  #Demod        : 1594
% 6.24/2.23  #Tautology    : 709
% 6.24/2.23  #SimpNegUnit  : 20
% 6.24/2.24  #BackRed      : 235
% 6.24/2.24  
% 6.24/2.24  #Partial instantiations: 0
% 6.24/2.24  #Strategies tried      : 1
% 6.24/2.24  
% 6.24/2.24  Timing (in seconds)
% 6.24/2.24  ----------------------
% 6.24/2.24  Preprocessing        : 0.36
% 6.24/2.24  Parsing              : 0.19
% 6.24/2.24  CNF conversion       : 0.03
% 6.24/2.24  Main loop            : 1.00
% 6.24/2.24  Inferencing          : 0.37
% 6.24/2.24  Reduction            : 0.34
% 6.24/2.24  Demodulation         : 0.24
% 6.24/2.24  BG Simplification    : 0.04
% 6.24/2.24  Subsumption          : 0.17
% 6.24/2.24  Abstraction          : 0.05
% 6.24/2.24  MUC search           : 0.00
% 6.24/2.24  Cooper               : 0.00
% 6.24/2.24  Total                : 1.46
% 6.24/2.24  Index Insertion      : 0.00
% 6.24/2.24  Index Deletion       : 0.00
% 6.24/2.24  Index Matching       : 0.00
% 6.24/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
