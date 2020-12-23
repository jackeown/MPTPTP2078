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
% DateTime   : Thu Dec  3 10:12:28 EST 2020

% Result     : Theorem 9.33s
% Output     : CNFRefutation 9.71s
% Verified   : 
% Statistics : Number of formulae       :  298 (7140 expanded)
%              Number of leaves         :   49 (2321 expanded)
%              Depth                    :   23
%              Number of atoms          :  537 (18118 expanded)
%              Number of equality atoms :  150 (3086 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_175,negated_conjecture,(
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

tff(f_109,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_135,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_158,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_148,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(c_86,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_6371,plain,(
    ! [C_9406,A_9407,B_9408] :
      ( v1_xboole_0(C_9406)
      | ~ m1_subset_1(C_9406,k1_zfmisc_1(k2_zfmisc_1(A_9407,B_9408)))
      | ~ v1_xboole_0(A_9407) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6388,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_6371])).

tff(c_6389,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6388])).

tff(c_6267,plain,(
    ! [C_9387,A_9388,B_9389] :
      ( v1_relat_1(C_9387)
      | ~ m1_subset_1(C_9387,k1_zfmisc_1(k2_zfmisc_1(A_9388,B_9389))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6285,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_6267])).

tff(c_90,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_84,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_82,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_6634,plain,(
    ! [A_9436,B_9437,C_9438] :
      ( k2_relset_1(A_9436,B_9437,C_9438) = k2_relat_1(C_9438)
      | ~ m1_subset_1(C_9438,k1_zfmisc_1(k2_zfmisc_1(A_9436,B_9437))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6650,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_6634])).

tff(c_6656,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6650])).

tff(c_40,plain,(
    ! [A_23] :
      ( k1_relat_1(k2_funct_1(A_23)) = k2_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_17] :
      ( v1_funct_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_80,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_119,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_122,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_119])).

tff(c_125,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_122])).

tff(c_200,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_207,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_200])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_207])).

tff(c_213,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_227,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_231,plain,(
    ~ r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_227])).

tff(c_312,plain,(
    ! [C_105,A_106,B_107] :
      ( v1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_326,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_312])).

tff(c_32,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_214,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_88,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_694,plain,(
    ! [A_159,B_160,C_161] :
      ( k1_relset_1(A_159,B_160,C_161) = k1_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_715,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_694])).

tff(c_2180,plain,(
    ! [B_255,A_256,C_257] :
      ( k1_xboole_0 = B_255
      | k1_relset_1(A_256,B_255,C_257) = A_256
      | ~ v1_funct_2(C_257,A_256,B_255)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_256,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2208,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_2180])).

tff(c_2221,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_715,c_2208])).

tff(c_2222,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2221])).

tff(c_799,plain,(
    ! [A_165,B_166,C_167] :
      ( k2_relset_1(A_165,B_166,C_167) = k2_relat_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_815,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_799])).

tff(c_820,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_815])).

tff(c_24,plain,(
    ! [A_14] :
      ( k9_relat_1(A_14,k1_relat_1(A_14)) = k2_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2252,plain,
    ( k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2222,c_24])).

tff(c_2262,plain,(
    k9_relat_1('#skF_6','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_820,c_2252])).

tff(c_36,plain,(
    ! [A_20,B_22] :
      ( k9_relat_1(k2_funct_1(A_20),k9_relat_1(A_20,B_22)) = B_22
      | ~ r1_tarski(B_22,k1_relat_1(A_20))
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2280,plain,
    ( k9_relat_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2262,c_36])).

tff(c_2284,plain,(
    k9_relat_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_90,c_84,c_18,c_2222,c_2280])).

tff(c_2292,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_6')),'#skF_4') = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2284,c_36])).

tff(c_2296,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_6')),'#skF_4') = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_2292])).

tff(c_3294,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2296])).

tff(c_3297,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_3294])).

tff(c_3301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_90,c_3297])).

tff(c_3303,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2296])).

tff(c_3302,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ r1_tarski('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_6')),'#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2296])).

tff(c_3509,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_3302])).

tff(c_3512,plain,
    ( ~ r1_tarski('#skF_5',k2_relat_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_3509])).

tff(c_3518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_90,c_84,c_18,c_820,c_3512])).

tff(c_3520,plain,(
    r1_tarski('#skF_5',k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_3302])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3534,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = '#skF_5'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_6')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_3520,c_14])).

tff(c_5414,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3534])).

tff(c_5417,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_5414])).

tff(c_5423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_90,c_84,c_18,c_820,c_5417])).

tff(c_5424,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3534])).

tff(c_5487,plain,
    ( k9_relat_1(k2_funct_1('#skF_6'),'#skF_5') = k2_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5424,c_24])).

tff(c_5505,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3303,c_2284,c_5487])).

tff(c_633,plain,(
    ! [A_152] :
      ( m1_subset_1(A_152,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_152),k2_relat_1(A_152))))
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_651,plain,(
    ! [A_152] :
      ( r1_tarski(A_152,k2_zfmisc_1(k1_relat_1(A_152),k2_relat_1(A_152)))
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(resolution,[status(thm)],[c_633,c_20])).

tff(c_5515,plain,
    ( r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),'#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5505,c_651])).

tff(c_5538,plain,(
    r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3303,c_214,c_5424,c_5515])).

tff(c_5540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_5538])).

tff(c_5541,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2221])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_393,plain,(
    ! [C_124,A_125,B_126] :
      ( v1_xboole_0(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_xboole_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_608,plain,(
    ! [A_149,A_150,B_151] :
      ( v1_xboole_0(A_149)
      | ~ v1_xboole_0(A_150)
      | ~ r1_tarski(A_149,k2_zfmisc_1(A_150,B_151)) ) ),
    inference(resolution,[status(thm)],[c_22,c_393])).

tff(c_652,plain,(
    ! [A_153,B_154] :
      ( v1_xboole_0(k2_zfmisc_1(A_153,B_154))
      | ~ v1_xboole_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_18,c_608])).

tff(c_221,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_2'(A_86,B_87),A_86)
      | r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_225,plain,(
    ! [A_86,B_87] :
      ( ~ v1_xboole_0(A_86)
      | r1_tarski(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_221,c_2])).

tff(c_243,plain,(
    ! [B_92,A_93] :
      ( B_92 = A_93
      | ~ r1_tarski(B_92,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_265,plain,(
    ! [B_95,A_96] :
      ( B_95 = A_96
      | ~ r1_tarski(B_95,A_96)
      | ~ v1_xboole_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_225,c_243])).

tff(c_279,plain,(
    ! [B_97,A_98] :
      ( B_97 = A_98
      | ~ v1_xboole_0(B_97)
      | ~ v1_xboole_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_225,c_265])).

tff(c_282,plain,(
    ! [A_98] :
      ( k1_xboole_0 = A_98
      | ~ v1_xboole_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_12,c_279])).

tff(c_684,plain,(
    ! [A_157,B_158] :
      ( k2_zfmisc_1(A_157,B_158) = k1_xboole_0
      | ~ v1_xboole_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_652,c_282])).

tff(c_693,plain,(
    ! [B_158] : k2_zfmisc_1(k1_xboole_0,B_158) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_684])).

tff(c_5576,plain,(
    ! [B_158] : k2_zfmisc_1('#skF_5',B_158) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5541,c_5541,c_693])).

tff(c_5738,plain,(
    ~ r1_tarski(k2_funct_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5576,c_231])).

tff(c_26,plain,(
    ! [A_15] :
      ( k10_relat_1(A_15,k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_830,plain,
    ( k10_relat_1('#skF_6','#skF_5') = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_26])).

tff(c_838,plain,(
    k10_relat_1('#skF_6','#skF_5') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_830])).

tff(c_1077,plain,(
    ! [B_181,A_182] :
      ( k9_relat_1(B_181,k10_relat_1(B_181,A_182)) = A_182
      | ~ r1_tarski(A_182,k2_relat_1(B_181))
      | ~ v1_funct_1(B_181)
      | ~ v1_relat_1(B_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1079,plain,(
    ! [A_182] :
      ( k9_relat_1('#skF_6',k10_relat_1('#skF_6',A_182)) = A_182
      | ~ r1_tarski(A_182,'#skF_5')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_1077])).

tff(c_1194,plain,(
    ! [A_191] :
      ( k9_relat_1('#skF_6',k10_relat_1('#skF_6',A_191)) = A_191
      | ~ r1_tarski(A_191,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_90,c_1079])).

tff(c_1203,plain,
    ( k9_relat_1('#skF_6',k1_relat_1('#skF_6')) = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_1194])).

tff(c_1211,plain,(
    k9_relat_1('#skF_6',k1_relat_1('#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1203])).

tff(c_2051,plain,(
    ! [A_238,B_239] :
      ( k9_relat_1(k2_funct_1(A_238),k9_relat_1(A_238,B_239)) = B_239
      | ~ r1_tarski(B_239,k1_relat_1(A_238))
      | ~ v2_funct_1(A_238)
      | ~ v1_funct_1(A_238)
      | ~ v1_relat_1(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2069,plain,
    ( k9_relat_1(k2_funct_1('#skF_6'),'#skF_5') = k1_relat_1('#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_6'),k1_relat_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1211,c_2051])).

tff(c_2081,plain,(
    k9_relat_1(k2_funct_1('#skF_6'),'#skF_5') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_90,c_84,c_18,c_2069])).

tff(c_2089,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_6')),k1_relat_1('#skF_6')) = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2081,c_36])).

tff(c_2093,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_6')),k1_relat_1('#skF_6')) = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_2089])).

tff(c_5936,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2093])).

tff(c_5939,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_5936])).

tff(c_5943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_90,c_5939])).

tff(c_5945,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2093])).

tff(c_5944,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ r1_tarski('#skF_5',k1_relat_1(k2_funct_1('#skF_6')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_6')),k1_relat_1('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2093])).

tff(c_5993,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_5944])).

tff(c_5996,plain,
    ( ~ r1_tarski('#skF_5',k2_relat_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_5993])).

tff(c_6002,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_90,c_84,c_18,c_820,c_5996])).

tff(c_6004,plain,(
    r1_tarski('#skF_5',k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_5944])).

tff(c_6019,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = '#skF_5'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_6')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6004,c_14])).

tff(c_6145,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6019])).

tff(c_6148,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_6145])).

tff(c_6154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_90,c_84,c_18,c_820,c_6148])).

tff(c_6155,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6019])).

tff(c_6162,plain,
    ( r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1('#skF_5',k2_relat_1(k2_funct_1('#skF_6'))))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6155,c_651])).

tff(c_6184,plain,(
    r1_tarski(k2_funct_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5945,c_214,c_5576,c_6162])).

tff(c_6186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5738,c_6184])).

tff(c_6187,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_6188,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_6597,plain,(
    ! [A_9432,B_9433,C_9434] :
      ( k1_relset_1(A_9432,B_9433,C_9434) = k1_relat_1(C_9434)
      | ~ m1_subset_1(C_9434,k1_zfmisc_1(k2_zfmisc_1(A_9432,B_9433))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6616,plain,(
    k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = k1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6188,c_6597])).

tff(c_7616,plain,(
    ! [B_9492,C_9493,A_9494] :
      ( k1_xboole_0 = B_9492
      | v1_funct_2(C_9493,A_9494,B_9492)
      | k1_relset_1(A_9494,B_9492,C_9493) != A_9494
      | ~ m1_subset_1(C_9493,k1_zfmisc_1(k2_zfmisc_1(A_9494,B_9492))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_7640,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_6188,c_7616])).

tff(c_7656,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6616,c_7640])).

tff(c_7657,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_6187,c_7656])).

tff(c_7661,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_7657])).

tff(c_7664,plain,
    ( k2_relat_1('#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_7661])).

tff(c_7667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6285,c_90,c_84,c_6656,c_7664])).

tff(c_7668,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7657])).

tff(c_7707,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7668,c_12])).

tff(c_7709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6389,c_7707])).

tff(c_7711,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_6388])).

tff(c_8090,plain,(
    ! [A_9523,A_9524,B_9525] :
      ( v1_xboole_0(A_9523)
      | ~ v1_xboole_0(A_9524)
      | ~ r1_tarski(A_9523,k2_zfmisc_1(A_9524,B_9525)) ) ),
    inference(resolution,[status(thm)],[c_22,c_6371])).

tff(c_8115,plain,(
    ! [A_9526,B_9527] :
      ( v1_xboole_0(k2_zfmisc_1(A_9526,B_9527))
      | ~ v1_xboole_0(A_9526) ) ),
    inference(resolution,[status(thm)],[c_18,c_8090])).

tff(c_114,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | ~ m1_subset_1(A_60,k1_zfmisc_1(B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_118,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_86,c_114])).

tff(c_6193,plain,(
    ! [B_9373,A_9374] :
      ( B_9373 = A_9374
      | ~ r1_tarski(B_9373,A_9374)
      | ~ r1_tarski(A_9374,B_9373) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6209,plain,(
    ! [B_9375,A_9376] :
      ( B_9375 = A_9376
      | ~ r1_tarski(B_9375,A_9376)
      | ~ v1_xboole_0(A_9376) ) ),
    inference(resolution,[status(thm)],[c_225,c_6193])).

tff(c_6224,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_118,c_6209])).

tff(c_6237,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6224])).

tff(c_8134,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_8115,c_6237])).

tff(c_8150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7711,c_8134])).

tff(c_8151,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6224])).

tff(c_8152,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6224])).

tff(c_8160,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8151,c_8152])).

tff(c_72,plain,(
    ! [A_40,B_41] : m1_subset_1('#skF_3'(A_40,B_41),k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_8414,plain,(
    ! [C_9558,A_9559,B_9560] :
      ( v1_xboole_0(C_9558)
      | ~ m1_subset_1(C_9558,k1_zfmisc_1(k2_zfmisc_1(A_9559,B_9560)))
      | ~ v1_xboole_0(A_9559) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_17915,plain,(
    ! [A_10031,B_10032] :
      ( v1_xboole_0('#skF_3'(A_10031,B_10032))
      | ~ v1_xboole_0(A_10031) ) ),
    inference(resolution,[status(thm)],[c_72,c_8414])).

tff(c_6223,plain,(
    ! [B_87,A_86] :
      ( B_87 = A_86
      | ~ v1_xboole_0(B_87)
      | ~ v1_xboole_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_225,c_6209])).

tff(c_8170,plain,(
    ! [A_86] :
      ( A_86 = '#skF_6'
      | ~ v1_xboole_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_8160,c_6223])).

tff(c_17938,plain,(
    ! [A_10033,B_10034] :
      ( '#skF_3'(A_10033,B_10034) = '#skF_6'
      | ~ v1_xboole_0(A_10033) ) ),
    inference(resolution,[status(thm)],[c_17915,c_8170])).

tff(c_17945,plain,(
    ! [B_10035] : '#skF_3'('#skF_6',B_10035) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_8160,c_17938])).

tff(c_62,plain,(
    ! [A_40,B_41] : v1_funct_2('#skF_3'(A_40,B_41),A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_17959,plain,(
    ! [B_10035] : v1_funct_2('#skF_6','#skF_6',B_10035) ),
    inference(superposition,[status(thm),theory(equality)],[c_17945,c_62])).

tff(c_6227,plain,(
    ! [B_9377,A_9378] :
      ( B_9377 = A_9378
      | ~ v1_xboole_0(B_9377)
      | ~ v1_xboole_0(A_9378) ) ),
    inference(resolution,[status(thm)],[c_225,c_6209])).

tff(c_6230,plain,(
    ! [A_9378] :
      ( k1_xboole_0 = A_9378
      | ~ v1_xboole_0(A_9378) ) ),
    inference(resolution,[status(thm)],[c_12,c_6227])).

tff(c_8169,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_8160,c_6230])).

tff(c_60,plain,(
    ! [B_38,A_37,C_39] :
      ( k1_xboole_0 = B_38
      | k1_relset_1(A_37,B_38,C_39) = A_37
      | ~ v1_funct_2(C_39,A_37,B_38)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_10703,plain,(
    ! [B_9720,A_9721,C_9722] :
      ( B_9720 = '#skF_6'
      | k1_relset_1(A_9721,B_9720,C_9722) = A_9721
      | ~ v1_funct_2(C_9722,A_9721,B_9720)
      | ~ m1_subset_1(C_9722,k1_zfmisc_1(k2_zfmisc_1(A_9721,B_9720))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8169,c_60])).

tff(c_10730,plain,(
    ! [C_9722] :
      ( '#skF_5' = '#skF_6'
      | k1_relset_1('#skF_4','#skF_5',C_9722) = '#skF_4'
      | ~ v1_funct_2(C_9722,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_9722,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8151,c_10703])).

tff(c_10895,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10730])).

tff(c_8429,plain,
    ( v1_xboole_0(k2_funct_1('#skF_6'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6188,c_8414])).

tff(c_8431,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8429])).

tff(c_10914,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10895,c_8431])).

tff(c_10926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8160,c_10914])).

tff(c_10928,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10730])).

tff(c_8420,plain,(
    ! [C_9558] :
      ( v1_xboole_0(C_9558)
      | ~ m1_subset_1(C_9558,k1_zfmisc_1('#skF_6'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8151,c_8414])).

tff(c_8547,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8420])).

tff(c_8154,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8151,c_86])).

tff(c_8650,plain,(
    ! [A_9583,A_9584,B_9585] :
      ( v1_xboole_0(A_9583)
      | ~ v1_xboole_0(A_9584)
      | ~ r1_tarski(A_9583,k2_zfmisc_1(A_9584,B_9585)) ) ),
    inference(resolution,[status(thm)],[c_22,c_8414])).

tff(c_8678,plain,(
    ! [A_9586,B_9587] :
      ( v1_xboole_0(k2_zfmisc_1(A_9586,B_9587))
      | ~ v1_xboole_0(A_9586) ) ),
    inference(resolution,[status(thm)],[c_18,c_8650])).

tff(c_8718,plain,(
    ! [A_9590,B_9591] :
      ( k2_zfmisc_1(A_9590,B_9591) = '#skF_6'
      | ~ v1_xboole_0(A_9590) ) ),
    inference(resolution,[status(thm)],[c_8678,c_8170])).

tff(c_8727,plain,(
    ! [B_9591] : k2_zfmisc_1('#skF_6',B_9591) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_8160,c_8718])).

tff(c_9091,plain,(
    ! [A_9616,B_9617,C_9618] :
      ( k1_relset_1(A_9616,B_9617,C_9618) = k1_relat_1(C_9618)
      | ~ m1_subset_1(C_9618,k1_zfmisc_1(k2_zfmisc_1(A_9616,B_9617))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_9472,plain,(
    ! [B_9640,C_9641] :
      ( k1_relset_1('#skF_6',B_9640,C_9641) = k1_relat_1(C_9641)
      | ~ m1_subset_1(C_9641,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8727,c_9091])).

tff(c_9478,plain,(
    ! [B_9640] : k1_relset_1('#skF_6',B_9640,'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8154,c_9472])).

tff(c_8432,plain,(
    ! [A_9561,B_9562] :
      ( v1_xboole_0('#skF_3'(A_9561,B_9562))
      | ~ v1_xboole_0(A_9561) ) ),
    inference(resolution,[status(thm)],[c_72,c_8414])).

tff(c_8454,plain,(
    ! [A_9563,B_9564] :
      ( '#skF_3'(A_9563,B_9564) = '#skF_6'
      | ~ v1_xboole_0(A_9563) ) ),
    inference(resolution,[status(thm)],[c_8432,c_8170])).

tff(c_8461,plain,(
    ! [B_9565] : '#skF_3'('#skF_6',B_9565) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_8160,c_8454])).

tff(c_8475,plain,(
    ! [B_9565] : v1_funct_2('#skF_6','#skF_6',B_9565) ),
    inference(superposition,[status(thm),theory(equality)],[c_8461,c_62])).

tff(c_58,plain,(
    ! [B_38,C_39] :
      ( k1_relset_1(k1_xboole_0,B_38,C_39) = k1_xboole_0
      | ~ v1_funct_2(C_39,k1_xboole_0,B_38)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_10191,plain,(
    ! [B_9690,C_9691] :
      ( k1_relset_1('#skF_6',B_9690,C_9691) = '#skF_6'
      | ~ v1_funct_2(C_9691,'#skF_6',B_9690)
      | ~ m1_subset_1(C_9691,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8727,c_8169,c_8169,c_8169,c_8169,c_58])).

tff(c_10196,plain,(
    ! [B_9565] :
      ( k1_relset_1('#skF_6',B_9565,'#skF_6') = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_8475,c_10191])).

tff(c_10206,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8154,c_9478,c_10196])).

tff(c_8236,plain,(
    ! [A_9536,B_9537] : m1_subset_1('#skF_3'(A_9536,B_9537),k1_zfmisc_1(k2_zfmisc_1(A_9536,B_9537))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_8245,plain,(
    m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8151,c_8236])).

tff(c_8263,plain,(
    r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_8245,c_20])).

tff(c_6203,plain,(
    ! [B_87,A_86] :
      ( B_87 = A_86
      | ~ r1_tarski(B_87,A_86)
      | ~ v1_xboole_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_225,c_6193])).

tff(c_8269,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_6'
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_8263,c_6203])).

tff(c_8276,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8160,c_8269])).

tff(c_9114,plain,(
    ! [A_40,B_41] : k1_relset_1(A_40,B_41,'#skF_3'(A_40,B_41)) = k1_relat_1('#skF_3'(A_40,B_41)) ),
    inference(resolution,[status(thm)],[c_72,c_9091])).

tff(c_10727,plain,(
    ! [B_41,A_40] :
      ( B_41 = '#skF_6'
      | k1_relset_1(A_40,B_41,'#skF_3'(A_40,B_41)) = A_40
      | ~ v1_funct_2('#skF_3'(A_40,B_41),A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_72,c_10703])).

tff(c_10751,plain,(
    ! [B_9723,A_9724] :
      ( B_9723 = '#skF_6'
      | k1_relat_1('#skF_3'(A_9724,B_9723)) = A_9724 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_9114,c_10727])).

tff(c_10791,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_8276,c_10751])).

tff(c_10809,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10206,c_10791])).

tff(c_10810,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10809])).

tff(c_10881,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10810,c_8160])).

tff(c_10892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8547,c_10881])).

tff(c_10893,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10809])).

tff(c_10929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10928,c_10893])).

tff(c_10931,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_8420])).

tff(c_10947,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10931,c_8170])).

tff(c_10971,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10947,c_6187])).

tff(c_8202,plain,(
    ! [C_9531,A_9532,B_9533] :
      ( v1_relat_1(C_9531)
      | ~ m1_subset_1(C_9531,k1_zfmisc_1(k2_zfmisc_1(A_9532,B_9533))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_8214,plain,(
    ! [C_9534] :
      ( v1_relat_1(C_9534)
      | ~ m1_subset_1(C_9534,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8151,c_8202])).

tff(c_8222,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8154,c_8214])).

tff(c_10961,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10947,c_8222])).

tff(c_28,plain,(
    ! [A_16] :
      ( v1_funct_1(A_16)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10949,plain,(
    v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10931,c_28])).

tff(c_10975,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10947,c_84])).

tff(c_8472,plain,(
    ! [B_9565] : m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_9565))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8461,c_72])).

tff(c_11311,plain,(
    ! [B_9745] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_9745))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10947,c_10947,c_8472])).

tff(c_48,plain,(
    ! [A_34,B_35,C_36] :
      ( k2_relset_1(A_34,B_35,C_36) = k2_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_11347,plain,(
    ! [B_9746] : k2_relset_1('#skF_4',B_9746,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11311,c_48])).

tff(c_10973,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10947,c_82])).

tff(c_11351,plain,(
    k2_relat_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_11347,c_10973])).

tff(c_8212,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6188,c_8202])).

tff(c_10963,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10947,c_8212])).

tff(c_10972,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10947,c_214])).

tff(c_10952,plain,(
    ! [B_9565] : v1_funct_2('#skF_4','#skF_4',B_9565) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10947,c_10947,c_8475])).

tff(c_46,plain,(
    ! [A_31,B_32,C_33] :
      ( k1_relset_1(A_31,B_32,C_33) = k1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_11334,plain,(
    ! [B_9745] : k1_relset_1('#skF_4',B_9745,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11311,c_46])).

tff(c_10950,plain,(
    ! [B_9565] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_9565))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10947,c_10947,c_8472])).

tff(c_10966,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10947,c_8169])).

tff(c_11826,plain,(
    ! [B_9777,C_9778] :
      ( k1_relset_1('#skF_4',B_9777,C_9778) = '#skF_4'
      | ~ v1_funct_2(C_9778,'#skF_4',B_9777)
      | ~ m1_subset_1(C_9778,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_9777))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10966,c_10966,c_10966,c_10966,c_58])).

tff(c_11833,plain,(
    ! [B_9565] :
      ( k1_relset_1('#skF_4',B_9565,'#skF_4') = '#skF_4'
      | ~ v1_funct_2('#skF_4','#skF_4',B_9565) ) ),
    inference(resolution,[status(thm)],[c_10950,c_11826])).

tff(c_11851,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10952,c_11334,c_11833])).

tff(c_11878,plain,
    ( k9_relat_1('#skF_4','#skF_4') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11851,c_24])).

tff(c_11886,plain,(
    k9_relat_1('#skF_4','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10961,c_11351,c_11878])).

tff(c_11953,plain,(
    ! [A_9784,B_9785] :
      ( k9_relat_1(k2_funct_1(A_9784),k9_relat_1(A_9784,B_9785)) = B_9785
      | ~ r1_tarski(B_9785,k1_relat_1(A_9784))
      | ~ v2_funct_1(A_9784)
      | ~ v1_funct_1(A_9784)
      | ~ v1_relat_1(A_9784) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_11968,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11886,c_11953])).

tff(c_11978,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10961,c_10949,c_10975,c_18,c_11851,c_11968])).

tff(c_8496,plain,(
    ! [A_9567] :
      ( k1_relat_1(k2_funct_1(A_9567)) = k2_relat_1(A_9567)
      | ~ v2_funct_1(A_9567)
      | ~ v1_funct_1(A_9567)
      | ~ v1_relat_1(A_9567) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_17565,plain,(
    ! [A_10028] :
      ( k9_relat_1(k2_funct_1(A_10028),k2_relat_1(A_10028)) = k2_relat_1(k2_funct_1(A_10028))
      | ~ v1_relat_1(k2_funct_1(A_10028))
      | ~ v2_funct_1(A_10028)
      | ~ v1_funct_1(A_10028)
      | ~ v1_relat_1(A_10028) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8496,c_24])).

tff(c_17598,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_5') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11351,c_17565])).

tff(c_17615,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10961,c_10949,c_10975,c_10963,c_11978,c_17598])).

tff(c_76,plain,(
    ! [A_43] :
      ( v1_funct_2(A_43,k1_relat_1(A_43),k2_relat_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_17646,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17615,c_76])).

tff(c_17674,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10963,c_10972,c_17646])).

tff(c_17686,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_17674])).

tff(c_17688,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10961,c_10949,c_10975,c_11351,c_17686])).

tff(c_17690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10971,c_17688])).

tff(c_17691,plain,(
    v1_xboole_0(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_8429])).

tff(c_17740,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_17691,c_8170])).

tff(c_17692,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_8429])).

tff(c_17705,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_17692,c_8170])).

tff(c_17717,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17705,c_6187])).

tff(c_17880,plain,(
    ~ v1_funct_2('#skF_6','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17740,c_17717])).

tff(c_17999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17959,c_17880])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.33/3.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.33/3.34  
% 9.33/3.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.33/3.34  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 9.33/3.34  
% 9.33/3.34  %Foreground sorts:
% 9.33/3.34  
% 9.33/3.34  
% 9.33/3.34  %Background operators:
% 9.33/3.34  
% 9.33/3.34  
% 9.33/3.34  %Foreground operators:
% 9.33/3.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.33/3.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.33/3.34  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.33/3.34  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.33/3.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.33/3.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.33/3.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.33/3.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.33/3.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.33/3.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.33/3.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.33/3.34  tff('#skF_5', type, '#skF_5': $i).
% 9.33/3.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.33/3.34  tff('#skF_6', type, '#skF_6': $i).
% 9.33/3.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.33/3.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.33/3.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.33/3.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.33/3.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.33/3.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.33/3.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.33/3.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.33/3.34  tff('#skF_4', type, '#skF_4': $i).
% 9.33/3.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.33/3.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.33/3.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.33/3.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.33/3.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.33/3.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.33/3.34  
% 9.71/3.38  tff(f_175, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 9.71/3.38  tff(f_109, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 9.71/3.38  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.71/3.38  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.71/3.38  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 9.71/3.38  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.71/3.38  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.71/3.38  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.71/3.38  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.71/3.38  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.71/3.38  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 9.71/3.38  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 9.71/3.38  tff(f_158, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 9.71/3.38  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.71/3.38  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.71/3.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.71/3.38  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 9.71/3.38  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 9.71/3.38  tff(f_148, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 9.71/3.38  tff(f_61, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 9.71/3.38  tff(c_86, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.71/3.38  tff(c_6371, plain, (![C_9406, A_9407, B_9408]: (v1_xboole_0(C_9406) | ~m1_subset_1(C_9406, k1_zfmisc_1(k2_zfmisc_1(A_9407, B_9408))) | ~v1_xboole_0(A_9407))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.71/3.38  tff(c_6388, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_86, c_6371])).
% 9.71/3.38  tff(c_6389, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_6388])).
% 9.71/3.38  tff(c_6267, plain, (![C_9387, A_9388, B_9389]: (v1_relat_1(C_9387) | ~m1_subset_1(C_9387, k1_zfmisc_1(k2_zfmisc_1(A_9388, B_9389))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.71/3.38  tff(c_6285, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_6267])).
% 9.71/3.38  tff(c_90, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.71/3.38  tff(c_84, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.71/3.38  tff(c_82, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.71/3.38  tff(c_6634, plain, (![A_9436, B_9437, C_9438]: (k2_relset_1(A_9436, B_9437, C_9438)=k2_relat_1(C_9438) | ~m1_subset_1(C_9438, k1_zfmisc_1(k2_zfmisc_1(A_9436, B_9437))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.71/3.38  tff(c_6650, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_6634])).
% 9.71/3.38  tff(c_6656, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_6650])).
% 9.71/3.38  tff(c_40, plain, (![A_23]: (k1_relat_1(k2_funct_1(A_23))=k2_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.71/3.38  tff(c_22, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.71/3.38  tff(c_30, plain, (![A_17]: (v1_funct_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.71/3.38  tff(c_80, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.71/3.38  tff(c_119, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_80])).
% 9.71/3.38  tff(c_122, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_119])).
% 9.71/3.38  tff(c_125, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_122])).
% 9.71/3.38  tff(c_200, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.71/3.38  tff(c_207, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_200])).
% 9.71/3.38  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_207])).
% 9.71/3.38  tff(c_213, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_80])).
% 9.71/3.38  tff(c_227, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_213])).
% 9.71/3.38  tff(c_231, plain, (~r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_227])).
% 9.71/3.38  tff(c_312, plain, (![C_105, A_106, B_107]: (v1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.71/3.38  tff(c_326, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_312])).
% 9.71/3.38  tff(c_32, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.71/3.38  tff(c_214, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_80])).
% 9.71/3.38  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.71/3.38  tff(c_88, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.71/3.38  tff(c_694, plain, (![A_159, B_160, C_161]: (k1_relset_1(A_159, B_160, C_161)=k1_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.71/3.38  tff(c_715, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_694])).
% 9.71/3.38  tff(c_2180, plain, (![B_255, A_256, C_257]: (k1_xboole_0=B_255 | k1_relset_1(A_256, B_255, C_257)=A_256 | ~v1_funct_2(C_257, A_256, B_255) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_256, B_255))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.71/3.38  tff(c_2208, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_86, c_2180])).
% 9.71/3.38  tff(c_2221, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_715, c_2208])).
% 9.71/3.38  tff(c_2222, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_2221])).
% 9.71/3.38  tff(c_799, plain, (![A_165, B_166, C_167]: (k2_relset_1(A_165, B_166, C_167)=k2_relat_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.71/3.38  tff(c_815, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_799])).
% 9.71/3.38  tff(c_820, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_815])).
% 9.71/3.38  tff(c_24, plain, (![A_14]: (k9_relat_1(A_14, k1_relat_1(A_14))=k2_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.71/3.38  tff(c_2252, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2222, c_24])).
% 9.71/3.38  tff(c_2262, plain, (k9_relat_1('#skF_6', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_820, c_2252])).
% 9.71/3.38  tff(c_36, plain, (![A_20, B_22]: (k9_relat_1(k2_funct_1(A_20), k9_relat_1(A_20, B_22))=B_22 | ~r1_tarski(B_22, k1_relat_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.71/3.38  tff(c_2280, plain, (k9_relat_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k1_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2262, c_36])).
% 9.71/3.38  tff(c_2284, plain, (k9_relat_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_90, c_84, c_18, c_2222, c_2280])).
% 9.71/3.38  tff(c_2292, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_6')), '#skF_4')='#skF_5' | ~r1_tarski('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2284, c_36])).
% 9.71/3.38  tff(c_2296, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_6')), '#skF_4')='#skF_5' | ~r1_tarski('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_2292])).
% 9.71/3.38  tff(c_3294, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2296])).
% 9.71/3.38  tff(c_3297, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_3294])).
% 9.71/3.38  tff(c_3301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_326, c_90, c_3297])).
% 9.71/3.38  tff(c_3303, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_2296])).
% 9.71/3.38  tff(c_3302, plain, (~v2_funct_1(k2_funct_1('#skF_6')) | ~r1_tarski('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_6')), '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_2296])).
% 9.71/3.38  tff(c_3509, plain, (~r1_tarski('#skF_5', k1_relat_1(k2_funct_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_3302])).
% 9.71/3.38  tff(c_3512, plain, (~r1_tarski('#skF_5', k2_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_40, c_3509])).
% 9.71/3.38  tff(c_3518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_326, c_90, c_84, c_18, c_820, c_3512])).
% 9.71/3.38  tff(c_3520, plain, (r1_tarski('#skF_5', k1_relat_1(k2_funct_1('#skF_6')))), inference(splitRight, [status(thm)], [c_3302])).
% 9.71/3.38  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.71/3.38  tff(c_3534, plain, (k1_relat_1(k2_funct_1('#skF_6'))='#skF_5' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_6')), '#skF_5')), inference(resolution, [status(thm)], [c_3520, c_14])).
% 9.71/3.38  tff(c_5414, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_3534])).
% 9.71/3.38  tff(c_5417, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_40, c_5414])).
% 9.71/3.38  tff(c_5423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_326, c_90, c_84, c_18, c_820, c_5417])).
% 9.71/3.38  tff(c_5424, plain, (k1_relat_1(k2_funct_1('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_3534])).
% 9.71/3.38  tff(c_5487, plain, (k9_relat_1(k2_funct_1('#skF_6'), '#skF_5')=k2_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5424, c_24])).
% 9.71/3.38  tff(c_5505, plain, (k2_relat_1(k2_funct_1('#skF_6'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3303, c_2284, c_5487])).
% 9.71/3.38  tff(c_633, plain, (![A_152]: (m1_subset_1(A_152, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_152), k2_relat_1(A_152)))) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.71/3.38  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.71/3.38  tff(c_651, plain, (![A_152]: (r1_tarski(A_152, k2_zfmisc_1(k1_relat_1(A_152), k2_relat_1(A_152))) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(resolution, [status(thm)], [c_633, c_20])).
% 9.71/3.38  tff(c_5515, plain, (r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), '#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5505, c_651])).
% 9.71/3.38  tff(c_5538, plain, (r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3303, c_214, c_5424, c_5515])).
% 9.71/3.38  tff(c_5540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_231, c_5538])).
% 9.71/3.38  tff(c_5541, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2221])).
% 9.71/3.38  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.71/3.38  tff(c_393, plain, (![C_124, A_125, B_126]: (v1_xboole_0(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_xboole_0(A_125))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.71/3.38  tff(c_608, plain, (![A_149, A_150, B_151]: (v1_xboole_0(A_149) | ~v1_xboole_0(A_150) | ~r1_tarski(A_149, k2_zfmisc_1(A_150, B_151)))), inference(resolution, [status(thm)], [c_22, c_393])).
% 9.71/3.38  tff(c_652, plain, (![A_153, B_154]: (v1_xboole_0(k2_zfmisc_1(A_153, B_154)) | ~v1_xboole_0(A_153))), inference(resolution, [status(thm)], [c_18, c_608])).
% 9.71/3.38  tff(c_221, plain, (![A_86, B_87]: (r2_hidden('#skF_2'(A_86, B_87), A_86) | r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.71/3.38  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.71/3.38  tff(c_225, plain, (![A_86, B_87]: (~v1_xboole_0(A_86) | r1_tarski(A_86, B_87))), inference(resolution, [status(thm)], [c_221, c_2])).
% 9.71/3.38  tff(c_243, plain, (![B_92, A_93]: (B_92=A_93 | ~r1_tarski(B_92, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.71/3.38  tff(c_265, plain, (![B_95, A_96]: (B_95=A_96 | ~r1_tarski(B_95, A_96) | ~v1_xboole_0(A_96))), inference(resolution, [status(thm)], [c_225, c_243])).
% 9.71/3.38  tff(c_279, plain, (![B_97, A_98]: (B_97=A_98 | ~v1_xboole_0(B_97) | ~v1_xboole_0(A_98))), inference(resolution, [status(thm)], [c_225, c_265])).
% 9.71/3.38  tff(c_282, plain, (![A_98]: (k1_xboole_0=A_98 | ~v1_xboole_0(A_98))), inference(resolution, [status(thm)], [c_12, c_279])).
% 9.71/3.38  tff(c_684, plain, (![A_157, B_158]: (k2_zfmisc_1(A_157, B_158)=k1_xboole_0 | ~v1_xboole_0(A_157))), inference(resolution, [status(thm)], [c_652, c_282])).
% 9.71/3.38  tff(c_693, plain, (![B_158]: (k2_zfmisc_1(k1_xboole_0, B_158)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_684])).
% 9.71/3.38  tff(c_5576, plain, (![B_158]: (k2_zfmisc_1('#skF_5', B_158)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5541, c_5541, c_693])).
% 9.71/3.38  tff(c_5738, plain, (~r1_tarski(k2_funct_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5576, c_231])).
% 9.71/3.38  tff(c_26, plain, (![A_15]: (k10_relat_1(A_15, k2_relat_1(A_15))=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.71/3.38  tff(c_830, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_820, c_26])).
% 9.71/3.38  tff(c_838, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_326, c_830])).
% 9.71/3.38  tff(c_1077, plain, (![B_181, A_182]: (k9_relat_1(B_181, k10_relat_1(B_181, A_182))=A_182 | ~r1_tarski(A_182, k2_relat_1(B_181)) | ~v1_funct_1(B_181) | ~v1_relat_1(B_181))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.71/3.38  tff(c_1079, plain, (![A_182]: (k9_relat_1('#skF_6', k10_relat_1('#skF_6', A_182))=A_182 | ~r1_tarski(A_182, '#skF_5') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_820, c_1077])).
% 9.71/3.38  tff(c_1194, plain, (![A_191]: (k9_relat_1('#skF_6', k10_relat_1('#skF_6', A_191))=A_191 | ~r1_tarski(A_191, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_90, c_1079])).
% 9.71/3.38  tff(c_1203, plain, (k9_relat_1('#skF_6', k1_relat_1('#skF_6'))='#skF_5' | ~r1_tarski('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_838, c_1194])).
% 9.71/3.38  tff(c_1211, plain, (k9_relat_1('#skF_6', k1_relat_1('#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1203])).
% 9.71/3.38  tff(c_2051, plain, (![A_238, B_239]: (k9_relat_1(k2_funct_1(A_238), k9_relat_1(A_238, B_239))=B_239 | ~r1_tarski(B_239, k1_relat_1(A_238)) | ~v2_funct_1(A_238) | ~v1_funct_1(A_238) | ~v1_relat_1(A_238))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.71/3.38  tff(c_2069, plain, (k9_relat_1(k2_funct_1('#skF_6'), '#skF_5')=k1_relat_1('#skF_6') | ~r1_tarski(k1_relat_1('#skF_6'), k1_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1211, c_2051])).
% 9.71/3.38  tff(c_2081, plain, (k9_relat_1(k2_funct_1('#skF_6'), '#skF_5')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_326, c_90, c_84, c_18, c_2069])).
% 9.71/3.38  tff(c_2089, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_6')), k1_relat_1('#skF_6'))='#skF_5' | ~r1_tarski('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2081, c_36])).
% 9.71/3.38  tff(c_2093, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_6')), k1_relat_1('#skF_6'))='#skF_5' | ~r1_tarski('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_2089])).
% 9.71/3.38  tff(c_5936, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2093])).
% 9.71/3.38  tff(c_5939, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_5936])).
% 9.71/3.38  tff(c_5943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_326, c_90, c_5939])).
% 9.71/3.38  tff(c_5945, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_2093])).
% 9.71/3.38  tff(c_5944, plain, (~v2_funct_1(k2_funct_1('#skF_6')) | ~r1_tarski('#skF_5', k1_relat_1(k2_funct_1('#skF_6'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_6')), k1_relat_1('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_2093])).
% 9.71/3.38  tff(c_5993, plain, (~r1_tarski('#skF_5', k1_relat_1(k2_funct_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_5944])).
% 9.71/3.38  tff(c_5996, plain, (~r1_tarski('#skF_5', k2_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_40, c_5993])).
% 9.71/3.38  tff(c_6002, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_326, c_90, c_84, c_18, c_820, c_5996])).
% 9.71/3.38  tff(c_6004, plain, (r1_tarski('#skF_5', k1_relat_1(k2_funct_1('#skF_6')))), inference(splitRight, [status(thm)], [c_5944])).
% 9.71/3.38  tff(c_6019, plain, (k1_relat_1(k2_funct_1('#skF_6'))='#skF_5' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_6')), '#skF_5')), inference(resolution, [status(thm)], [c_6004, c_14])).
% 9.71/3.38  tff(c_6145, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_6019])).
% 9.71/3.38  tff(c_6148, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_40, c_6145])).
% 9.71/3.38  tff(c_6154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_326, c_90, c_84, c_18, c_820, c_6148])).
% 9.71/3.38  tff(c_6155, plain, (k1_relat_1(k2_funct_1('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_6019])).
% 9.71/3.38  tff(c_6162, plain, (r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1('#skF_5', k2_relat_1(k2_funct_1('#skF_6')))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6155, c_651])).
% 9.71/3.38  tff(c_6184, plain, (r1_tarski(k2_funct_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5945, c_214, c_5576, c_6162])).
% 9.71/3.38  tff(c_6186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5738, c_6184])).
% 9.71/3.38  tff(c_6187, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_213])).
% 9.71/3.38  tff(c_6188, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_213])).
% 9.71/3.38  tff(c_6597, plain, (![A_9432, B_9433, C_9434]: (k1_relset_1(A_9432, B_9433, C_9434)=k1_relat_1(C_9434) | ~m1_subset_1(C_9434, k1_zfmisc_1(k2_zfmisc_1(A_9432, B_9433))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.71/3.38  tff(c_6616, plain, (k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))=k1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_6188, c_6597])).
% 9.71/3.38  tff(c_7616, plain, (![B_9492, C_9493, A_9494]: (k1_xboole_0=B_9492 | v1_funct_2(C_9493, A_9494, B_9492) | k1_relset_1(A_9494, B_9492, C_9493)!=A_9494 | ~m1_subset_1(C_9493, k1_zfmisc_1(k2_zfmisc_1(A_9494, B_9492))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.71/3.38  tff(c_7640, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))!='#skF_5'), inference(resolution, [status(thm)], [c_6188, c_7616])).
% 9.71/3.38  tff(c_7656, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6616, c_7640])).
% 9.71/3.38  tff(c_7657, plain, (k1_xboole_0='#skF_4' | k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_6187, c_7656])).
% 9.71/3.38  tff(c_7661, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_7657])).
% 9.71/3.38  tff(c_7664, plain, (k2_relat_1('#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_40, c_7661])).
% 9.71/3.38  tff(c_7667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6285, c_90, c_84, c_6656, c_7664])).
% 9.71/3.38  tff(c_7668, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_7657])).
% 9.71/3.38  tff(c_7707, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7668, c_12])).
% 9.71/3.38  tff(c_7709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6389, c_7707])).
% 9.71/3.38  tff(c_7711, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_6388])).
% 9.71/3.38  tff(c_8090, plain, (![A_9523, A_9524, B_9525]: (v1_xboole_0(A_9523) | ~v1_xboole_0(A_9524) | ~r1_tarski(A_9523, k2_zfmisc_1(A_9524, B_9525)))), inference(resolution, [status(thm)], [c_22, c_6371])).
% 9.71/3.38  tff(c_8115, plain, (![A_9526, B_9527]: (v1_xboole_0(k2_zfmisc_1(A_9526, B_9527)) | ~v1_xboole_0(A_9526))), inference(resolution, [status(thm)], [c_18, c_8090])).
% 9.71/3.38  tff(c_114, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | ~m1_subset_1(A_60, k1_zfmisc_1(B_61)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.71/3.38  tff(c_118, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_86, c_114])).
% 9.71/3.38  tff(c_6193, plain, (![B_9373, A_9374]: (B_9373=A_9374 | ~r1_tarski(B_9373, A_9374) | ~r1_tarski(A_9374, B_9373))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.71/3.38  tff(c_6209, plain, (![B_9375, A_9376]: (B_9375=A_9376 | ~r1_tarski(B_9375, A_9376) | ~v1_xboole_0(A_9376))), inference(resolution, [status(thm)], [c_225, c_6193])).
% 9.71/3.38  tff(c_6224, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_118, c_6209])).
% 9.71/3.38  tff(c_6237, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_6224])).
% 9.71/3.38  tff(c_8134, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_8115, c_6237])).
% 9.71/3.38  tff(c_8150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7711, c_8134])).
% 9.71/3.38  tff(c_8151, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_6224])).
% 9.71/3.38  tff(c_8152, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_6224])).
% 9.71/3.38  tff(c_8160, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8151, c_8152])).
% 9.71/3.38  tff(c_72, plain, (![A_40, B_41]: (m1_subset_1('#skF_3'(A_40, B_41), k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.71/3.38  tff(c_8414, plain, (![C_9558, A_9559, B_9560]: (v1_xboole_0(C_9558) | ~m1_subset_1(C_9558, k1_zfmisc_1(k2_zfmisc_1(A_9559, B_9560))) | ~v1_xboole_0(A_9559))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.71/3.38  tff(c_17915, plain, (![A_10031, B_10032]: (v1_xboole_0('#skF_3'(A_10031, B_10032)) | ~v1_xboole_0(A_10031))), inference(resolution, [status(thm)], [c_72, c_8414])).
% 9.71/3.38  tff(c_6223, plain, (![B_87, A_86]: (B_87=A_86 | ~v1_xboole_0(B_87) | ~v1_xboole_0(A_86))), inference(resolution, [status(thm)], [c_225, c_6209])).
% 9.71/3.38  tff(c_8170, plain, (![A_86]: (A_86='#skF_6' | ~v1_xboole_0(A_86))), inference(resolution, [status(thm)], [c_8160, c_6223])).
% 9.71/3.38  tff(c_17938, plain, (![A_10033, B_10034]: ('#skF_3'(A_10033, B_10034)='#skF_6' | ~v1_xboole_0(A_10033))), inference(resolution, [status(thm)], [c_17915, c_8170])).
% 9.71/3.38  tff(c_17945, plain, (![B_10035]: ('#skF_3'('#skF_6', B_10035)='#skF_6')), inference(resolution, [status(thm)], [c_8160, c_17938])).
% 9.71/3.38  tff(c_62, plain, (![A_40, B_41]: (v1_funct_2('#skF_3'(A_40, B_41), A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.71/3.38  tff(c_17959, plain, (![B_10035]: (v1_funct_2('#skF_6', '#skF_6', B_10035))), inference(superposition, [status(thm), theory('equality')], [c_17945, c_62])).
% 9.71/3.38  tff(c_6227, plain, (![B_9377, A_9378]: (B_9377=A_9378 | ~v1_xboole_0(B_9377) | ~v1_xboole_0(A_9378))), inference(resolution, [status(thm)], [c_225, c_6209])).
% 9.71/3.38  tff(c_6230, plain, (![A_9378]: (k1_xboole_0=A_9378 | ~v1_xboole_0(A_9378))), inference(resolution, [status(thm)], [c_12, c_6227])).
% 9.71/3.38  tff(c_8169, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_8160, c_6230])).
% 9.71/3.38  tff(c_60, plain, (![B_38, A_37, C_39]: (k1_xboole_0=B_38 | k1_relset_1(A_37, B_38, C_39)=A_37 | ~v1_funct_2(C_39, A_37, B_38) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.71/3.38  tff(c_10703, plain, (![B_9720, A_9721, C_9722]: (B_9720='#skF_6' | k1_relset_1(A_9721, B_9720, C_9722)=A_9721 | ~v1_funct_2(C_9722, A_9721, B_9720) | ~m1_subset_1(C_9722, k1_zfmisc_1(k2_zfmisc_1(A_9721, B_9720))))), inference(demodulation, [status(thm), theory('equality')], [c_8169, c_60])).
% 9.71/3.38  tff(c_10730, plain, (![C_9722]: ('#skF_5'='#skF_6' | k1_relset_1('#skF_4', '#skF_5', C_9722)='#skF_4' | ~v1_funct_2(C_9722, '#skF_4', '#skF_5') | ~m1_subset_1(C_9722, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_8151, c_10703])).
% 9.71/3.38  tff(c_10895, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_10730])).
% 9.71/3.38  tff(c_8429, plain, (v1_xboole_0(k2_funct_1('#skF_6')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_6188, c_8414])).
% 9.71/3.38  tff(c_8431, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_8429])).
% 9.71/3.38  tff(c_10914, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10895, c_8431])).
% 9.71/3.38  tff(c_10926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8160, c_10914])).
% 9.71/3.38  tff(c_10928, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_10730])).
% 9.71/3.38  tff(c_8420, plain, (![C_9558]: (v1_xboole_0(C_9558) | ~m1_subset_1(C_9558, k1_zfmisc_1('#skF_6')) | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8151, c_8414])).
% 9.71/3.38  tff(c_8547, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_8420])).
% 9.71/3.38  tff(c_8154, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_8151, c_86])).
% 9.71/3.38  tff(c_8650, plain, (![A_9583, A_9584, B_9585]: (v1_xboole_0(A_9583) | ~v1_xboole_0(A_9584) | ~r1_tarski(A_9583, k2_zfmisc_1(A_9584, B_9585)))), inference(resolution, [status(thm)], [c_22, c_8414])).
% 9.71/3.38  tff(c_8678, plain, (![A_9586, B_9587]: (v1_xboole_0(k2_zfmisc_1(A_9586, B_9587)) | ~v1_xboole_0(A_9586))), inference(resolution, [status(thm)], [c_18, c_8650])).
% 9.71/3.38  tff(c_8718, plain, (![A_9590, B_9591]: (k2_zfmisc_1(A_9590, B_9591)='#skF_6' | ~v1_xboole_0(A_9590))), inference(resolution, [status(thm)], [c_8678, c_8170])).
% 9.71/3.38  tff(c_8727, plain, (![B_9591]: (k2_zfmisc_1('#skF_6', B_9591)='#skF_6')), inference(resolution, [status(thm)], [c_8160, c_8718])).
% 9.71/3.38  tff(c_9091, plain, (![A_9616, B_9617, C_9618]: (k1_relset_1(A_9616, B_9617, C_9618)=k1_relat_1(C_9618) | ~m1_subset_1(C_9618, k1_zfmisc_1(k2_zfmisc_1(A_9616, B_9617))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.71/3.38  tff(c_9472, plain, (![B_9640, C_9641]: (k1_relset_1('#skF_6', B_9640, C_9641)=k1_relat_1(C_9641) | ~m1_subset_1(C_9641, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_8727, c_9091])).
% 9.71/3.38  tff(c_9478, plain, (![B_9640]: (k1_relset_1('#skF_6', B_9640, '#skF_6')=k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_8154, c_9472])).
% 9.71/3.38  tff(c_8432, plain, (![A_9561, B_9562]: (v1_xboole_0('#skF_3'(A_9561, B_9562)) | ~v1_xboole_0(A_9561))), inference(resolution, [status(thm)], [c_72, c_8414])).
% 9.71/3.38  tff(c_8454, plain, (![A_9563, B_9564]: ('#skF_3'(A_9563, B_9564)='#skF_6' | ~v1_xboole_0(A_9563))), inference(resolution, [status(thm)], [c_8432, c_8170])).
% 9.71/3.38  tff(c_8461, plain, (![B_9565]: ('#skF_3'('#skF_6', B_9565)='#skF_6')), inference(resolution, [status(thm)], [c_8160, c_8454])).
% 9.71/3.38  tff(c_8475, plain, (![B_9565]: (v1_funct_2('#skF_6', '#skF_6', B_9565))), inference(superposition, [status(thm), theory('equality')], [c_8461, c_62])).
% 9.71/3.38  tff(c_58, plain, (![B_38, C_39]: (k1_relset_1(k1_xboole_0, B_38, C_39)=k1_xboole_0 | ~v1_funct_2(C_39, k1_xboole_0, B_38) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_38))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.71/3.38  tff(c_10191, plain, (![B_9690, C_9691]: (k1_relset_1('#skF_6', B_9690, C_9691)='#skF_6' | ~v1_funct_2(C_9691, '#skF_6', B_9690) | ~m1_subset_1(C_9691, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_8727, c_8169, c_8169, c_8169, c_8169, c_58])).
% 9.71/3.38  tff(c_10196, plain, (![B_9565]: (k1_relset_1('#skF_6', B_9565, '#skF_6')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_8475, c_10191])).
% 9.71/3.38  tff(c_10206, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8154, c_9478, c_10196])).
% 9.71/3.38  tff(c_8236, plain, (![A_9536, B_9537]: (m1_subset_1('#skF_3'(A_9536, B_9537), k1_zfmisc_1(k2_zfmisc_1(A_9536, B_9537))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.71/3.38  tff(c_8245, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8151, c_8236])).
% 9.71/3.38  tff(c_8263, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_8245, c_20])).
% 9.71/3.38  tff(c_6203, plain, (![B_87, A_86]: (B_87=A_86 | ~r1_tarski(B_87, A_86) | ~v1_xboole_0(A_86))), inference(resolution, [status(thm)], [c_225, c_6193])).
% 9.71/3.38  tff(c_8269, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_6' | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_8263, c_6203])).
% 9.71/3.38  tff(c_8276, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8160, c_8269])).
% 9.71/3.38  tff(c_9114, plain, (![A_40, B_41]: (k1_relset_1(A_40, B_41, '#skF_3'(A_40, B_41))=k1_relat_1('#skF_3'(A_40, B_41)))), inference(resolution, [status(thm)], [c_72, c_9091])).
% 9.71/3.38  tff(c_10727, plain, (![B_41, A_40]: (B_41='#skF_6' | k1_relset_1(A_40, B_41, '#skF_3'(A_40, B_41))=A_40 | ~v1_funct_2('#skF_3'(A_40, B_41), A_40, B_41))), inference(resolution, [status(thm)], [c_72, c_10703])).
% 9.71/3.38  tff(c_10751, plain, (![B_9723, A_9724]: (B_9723='#skF_6' | k1_relat_1('#skF_3'(A_9724, B_9723))=A_9724)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_9114, c_10727])).
% 9.71/3.38  tff(c_10791, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_6')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_8276, c_10751])).
% 9.71/3.38  tff(c_10809, plain, ('#skF_5'='#skF_6' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10206, c_10791])).
% 9.71/3.38  tff(c_10810, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_10809])).
% 9.71/3.38  tff(c_10881, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10810, c_8160])).
% 9.71/3.38  tff(c_10892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8547, c_10881])).
% 9.71/3.38  tff(c_10893, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_10809])).
% 9.71/3.38  tff(c_10929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10928, c_10893])).
% 9.71/3.38  tff(c_10931, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_8420])).
% 9.71/3.38  tff(c_10947, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_10931, c_8170])).
% 9.71/3.38  tff(c_10971, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10947, c_6187])).
% 9.71/3.38  tff(c_8202, plain, (![C_9531, A_9532, B_9533]: (v1_relat_1(C_9531) | ~m1_subset_1(C_9531, k1_zfmisc_1(k2_zfmisc_1(A_9532, B_9533))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.71/3.38  tff(c_8214, plain, (![C_9534]: (v1_relat_1(C_9534) | ~m1_subset_1(C_9534, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_8151, c_8202])).
% 9.71/3.38  tff(c_8222, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8154, c_8214])).
% 9.71/3.38  tff(c_10961, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10947, c_8222])).
% 9.71/3.38  tff(c_28, plain, (![A_16]: (v1_funct_1(A_16) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.71/3.38  tff(c_10949, plain, (v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_10931, c_28])).
% 9.71/3.38  tff(c_10975, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10947, c_84])).
% 9.71/3.38  tff(c_8472, plain, (![B_9565]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_9565))))), inference(superposition, [status(thm), theory('equality')], [c_8461, c_72])).
% 9.71/3.38  tff(c_11311, plain, (![B_9745]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_9745))))), inference(demodulation, [status(thm), theory('equality')], [c_10947, c_10947, c_8472])).
% 9.71/3.38  tff(c_48, plain, (![A_34, B_35, C_36]: (k2_relset_1(A_34, B_35, C_36)=k2_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.71/3.38  tff(c_11347, plain, (![B_9746]: (k2_relset_1('#skF_4', B_9746, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_11311, c_48])).
% 9.71/3.38  tff(c_10973, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_10947, c_82])).
% 9.71/3.38  tff(c_11351, plain, (k2_relat_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_11347, c_10973])).
% 9.71/3.38  tff(c_8212, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_6188, c_8202])).
% 9.71/3.38  tff(c_10963, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10947, c_8212])).
% 9.71/3.38  tff(c_10972, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10947, c_214])).
% 9.71/3.38  tff(c_10952, plain, (![B_9565]: (v1_funct_2('#skF_4', '#skF_4', B_9565))), inference(demodulation, [status(thm), theory('equality')], [c_10947, c_10947, c_8475])).
% 9.71/3.38  tff(c_46, plain, (![A_31, B_32, C_33]: (k1_relset_1(A_31, B_32, C_33)=k1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.71/3.38  tff(c_11334, plain, (![B_9745]: (k1_relset_1('#skF_4', B_9745, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_11311, c_46])).
% 9.71/3.38  tff(c_10950, plain, (![B_9565]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_9565))))), inference(demodulation, [status(thm), theory('equality')], [c_10947, c_10947, c_8472])).
% 9.71/3.38  tff(c_10966, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10947, c_8169])).
% 9.71/3.38  tff(c_11826, plain, (![B_9777, C_9778]: (k1_relset_1('#skF_4', B_9777, C_9778)='#skF_4' | ~v1_funct_2(C_9778, '#skF_4', B_9777) | ~m1_subset_1(C_9778, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_9777))))), inference(demodulation, [status(thm), theory('equality')], [c_10966, c_10966, c_10966, c_10966, c_58])).
% 9.71/3.38  tff(c_11833, plain, (![B_9565]: (k1_relset_1('#skF_4', B_9565, '#skF_4')='#skF_4' | ~v1_funct_2('#skF_4', '#skF_4', B_9565))), inference(resolution, [status(thm)], [c_10950, c_11826])).
% 9.71/3.38  tff(c_11851, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10952, c_11334, c_11833])).
% 9.71/3.38  tff(c_11878, plain, (k9_relat_1('#skF_4', '#skF_4')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11851, c_24])).
% 9.71/3.38  tff(c_11886, plain, (k9_relat_1('#skF_4', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_10961, c_11351, c_11878])).
% 9.71/3.38  tff(c_11953, plain, (![A_9784, B_9785]: (k9_relat_1(k2_funct_1(A_9784), k9_relat_1(A_9784, B_9785))=B_9785 | ~r1_tarski(B_9785, k1_relat_1(A_9784)) | ~v2_funct_1(A_9784) | ~v1_funct_1(A_9784) | ~v1_relat_1(A_9784))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.71/3.38  tff(c_11968, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11886, c_11953])).
% 9.71/3.38  tff(c_11978, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10961, c_10949, c_10975, c_18, c_11851, c_11968])).
% 9.71/3.38  tff(c_8496, plain, (![A_9567]: (k1_relat_1(k2_funct_1(A_9567))=k2_relat_1(A_9567) | ~v2_funct_1(A_9567) | ~v1_funct_1(A_9567) | ~v1_relat_1(A_9567))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.71/3.38  tff(c_17565, plain, (![A_10028]: (k9_relat_1(k2_funct_1(A_10028), k2_relat_1(A_10028))=k2_relat_1(k2_funct_1(A_10028)) | ~v1_relat_1(k2_funct_1(A_10028)) | ~v2_funct_1(A_10028) | ~v1_funct_1(A_10028) | ~v1_relat_1(A_10028))), inference(superposition, [status(thm), theory('equality')], [c_8496, c_24])).
% 9.71/3.38  tff(c_17598, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_5')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11351, c_17565])).
% 9.71/3.38  tff(c_17615, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10961, c_10949, c_10975, c_10963, c_11978, c_17598])).
% 9.71/3.38  tff(c_76, plain, (![A_43]: (v1_funct_2(A_43, k1_relat_1(A_43), k2_relat_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.71/3.38  tff(c_17646, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_17615, c_76])).
% 9.71/3.38  tff(c_17674, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10963, c_10972, c_17646])).
% 9.71/3.38  tff(c_17686, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_40, c_17674])).
% 9.71/3.38  tff(c_17688, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10961, c_10949, c_10975, c_11351, c_17686])).
% 9.71/3.38  tff(c_17690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10971, c_17688])).
% 9.71/3.38  tff(c_17691, plain, (v1_xboole_0(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_8429])).
% 9.71/3.38  tff(c_17740, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_17691, c_8170])).
% 9.71/3.38  tff(c_17692, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_8429])).
% 9.71/3.38  tff(c_17705, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_17692, c_8170])).
% 9.71/3.38  tff(c_17717, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17705, c_6187])).
% 9.71/3.38  tff(c_17880, plain, (~v1_funct_2('#skF_6', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17740, c_17717])).
% 9.71/3.38  tff(c_17999, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17959, c_17880])).
% 9.71/3.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.71/3.38  
% 9.71/3.38  Inference rules
% 9.71/3.38  ----------------------
% 9.71/3.38  #Ref     : 0
% 9.71/3.38  #Sup     : 3988
% 9.71/3.38  #Fact    : 4
% 9.71/3.38  #Define  : 0
% 9.71/3.38  #Split   : 39
% 9.71/3.38  #Chain   : 0
% 9.71/3.38  #Close   : 0
% 9.71/3.38  
% 9.71/3.38  Ordering : KBO
% 9.71/3.38  
% 9.71/3.38  Simplification rules
% 9.71/3.38  ----------------------
% 9.71/3.38  #Subsume      : 856
% 9.71/3.38  #Demod        : 3433
% 9.71/3.38  #Tautology    : 1762
% 9.71/3.38  #SimpNegUnit  : 10
% 9.71/3.38  #BackRed      : 319
% 9.71/3.38  
% 9.71/3.38  #Partial instantiations: 1281
% 9.71/3.38  #Strategies tried      : 1
% 9.71/3.38  
% 9.71/3.38  Timing (in seconds)
% 9.71/3.38  ----------------------
% 9.71/3.38  Preprocessing        : 0.36
% 9.71/3.38  Parsing              : 0.19
% 9.71/3.38  CNF conversion       : 0.03
% 9.71/3.38  Main loop            : 2.19
% 9.71/3.38  Inferencing          : 0.75
% 9.71/3.38  Reduction            : 0.72
% 9.71/3.38  Demodulation         : 0.51
% 9.71/3.38  BG Simplification    : 0.08
% 9.71/3.38  Subsumption          : 0.46
% 9.71/3.38  Abstraction          : 0.10
% 9.71/3.38  MUC search           : 0.00
% 9.71/3.38  Cooper               : 0.00
% 9.71/3.38  Total                : 2.64
% 9.71/3.38  Index Insertion      : 0.00
% 9.71/3.38  Index Deletion       : 0.00
% 9.71/3.38  Index Matching       : 0.00
% 9.71/3.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
