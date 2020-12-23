%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:19 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.06s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 151 expanded)
%              Number of leaves         :   40 (  68 expanded)
%              Depth                    :    6
%              Number of atoms          :  150 ( 394 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(A))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(B))
                       => ( r1_tarski(k7_relset_1(A,B,C,D),E)
                        <=> r1_tarski(D,k8_relset_1(A,B,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_36,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4222,plain,(
    ! [A_321,B_322,C_323,D_324] :
      ( k8_relset_1(A_321,B_322,C_323,D_324) = k10_relat_1(C_323,D_324)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4232,plain,(
    ! [D_324] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_324) = k10_relat_1('#skF_4',D_324) ),
    inference(resolution,[status(thm)],[c_46,c_4222])).

tff(c_91,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_104,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_91])).

tff(c_862,plain,(
    ! [A_136,B_137,C_138,D_139] :
      ( k8_relset_1(A_136,B_137,C_138,D_139) = k10_relat_1(C_138,D_139)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_872,plain,(
    ! [D_139] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_139) = k10_relat_1('#skF_4',D_139) ),
    inference(resolution,[status(thm)],[c_46,c_862])).

tff(c_56,plain,
    ( ~ r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6'))
    | ~ r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_65,plain,(
    ~ r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,
    ( r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_106,plain,(
    r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_62])).

tff(c_876,plain,(
    r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_106])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_14,plain,(
    ! [C_13,A_11,B_12] :
      ( r1_tarski(k9_relat_1(C_13,A_11),k9_relat_1(C_13,B_12))
      | ~ r1_tarski(A_11,B_12)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_253,plain,(
    ! [B_93,A_94] :
      ( r1_tarski(k9_relat_1(B_93,k10_relat_1(B_93,A_94)),A_94)
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2849,plain,(
    ! [A_244,A_245,B_246] :
      ( r1_tarski(A_244,A_245)
      | ~ r1_tarski(A_244,k9_relat_1(B_246,k10_relat_1(B_246,A_245)))
      | ~ v1_funct_1(B_246)
      | ~ v1_relat_1(B_246) ) ),
    inference(resolution,[status(thm)],[c_253,c_2])).

tff(c_3358,plain,(
    ! [C_262,A_263,A_264] :
      ( r1_tarski(k9_relat_1(C_262,A_263),A_264)
      | ~ v1_funct_1(C_262)
      | ~ r1_tarski(A_263,k10_relat_1(C_262,A_264))
      | ~ v1_relat_1(C_262) ) ),
    inference(resolution,[status(thm)],[c_14,c_2849])).

tff(c_738,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( k7_relset_1(A_124,B_125,C_126,D_127) = k9_relat_1(C_126,D_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_748,plain,(
    ! [D_127] : k7_relset_1('#skF_2','#skF_3','#skF_4',D_127) = k9_relat_1('#skF_4',D_127) ),
    inference(resolution,[status(thm)],[c_46,c_738])).

tff(c_750,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_65])).

tff(c_3443,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3358,c_750])).

tff(c_3506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_876,c_50,c_3443])).

tff(c_3507,plain,(
    ~ r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_4234,plain,(
    ~ r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4232,c_3507])).

tff(c_3535,plain,(
    ! [C_272,A_273,B_274] :
      ( v1_relat_1(C_272)
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(A_273,B_274))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3548,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_3535])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3511,plain,(
    ! [A_269,B_270] :
      ( r1_tarski(A_269,B_270)
      | ~ m1_subset_1(A_269,k1_zfmisc_1(B_270)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3532,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_3511])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3874,plain,(
    ! [A_301,B_302,C_303] :
      ( k1_relset_1(A_301,B_302,C_303) = k1_relat_1(C_303)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3887,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_3874])).

tff(c_4807,plain,(
    ! [B_352,A_353,C_354] :
      ( k1_xboole_0 = B_352
      | k1_relset_1(A_353,B_352,C_354) = A_353
      | ~ v1_funct_2(C_354,A_353,B_352)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(A_353,B_352))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4814,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_4807])).

tff(c_4822,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3887,c_4814])).

tff(c_4824,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4822])).

tff(c_4352,plain,(
    ! [A_329,B_330,C_331,D_332] :
      ( k7_relset_1(A_329,B_330,C_331,D_332) = k9_relat_1(C_331,D_332)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4362,plain,(
    ! [D_332] : k7_relset_1('#skF_2','#skF_3','#skF_4',D_332) = k9_relat_1('#skF_4',D_332) ),
    inference(resolution,[status(thm)],[c_46,c_4352])).

tff(c_3508,plain,(
    r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_4370,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4362,c_3508])).

tff(c_5213,plain,(
    ! [A_376,C_377,B_378] :
      ( r1_tarski(A_376,k10_relat_1(C_377,B_378))
      | ~ r1_tarski(k9_relat_1(C_377,A_376),B_378)
      | ~ r1_tarski(A_376,k1_relat_1(C_377))
      | ~ v1_funct_1(C_377)
      | ~ v1_relat_1(C_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5234,plain,
    ( r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4370,c_5213])).

tff(c_5259,plain,(
    r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3548,c_50,c_3532,c_4824,c_5234])).

tff(c_5261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4234,c_5259])).

tff(c_5262,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4822])).

tff(c_6,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3568,plain,(
    ! [A_280,B_281] :
      ( r2_hidden(A_280,B_281)
      | v1_xboole_0(B_281)
      | ~ m1_subset_1(A_280,B_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3573,plain,(
    ! [B_282,A_283] :
      ( ~ r1_tarski(B_282,A_283)
      | v1_xboole_0(B_282)
      | ~ m1_subset_1(A_283,B_282) ) ),
    inference(resolution,[status(thm)],[c_3568,c_20])).

tff(c_3597,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_3573])).

tff(c_3601,plain,(
    ! [A_284] : ~ m1_subset_1(A_284,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3597])).

tff(c_3606,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_3601])).

tff(c_3607,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3597])).

tff(c_5278,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5262,c_3607])).

tff(c_5282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_5278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.06/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.28  
% 6.06/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.28  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 6.06/2.28  
% 6.06/2.28  %Foreground sorts:
% 6.06/2.28  
% 6.06/2.28  
% 6.06/2.28  %Background operators:
% 6.06/2.28  
% 6.06/2.28  
% 6.06/2.28  %Foreground operators:
% 6.06/2.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.06/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.06/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.06/2.28  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 6.06/2.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.06/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.06/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.06/2.28  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.06/2.28  tff('#skF_5', type, '#skF_5': $i).
% 6.06/2.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.06/2.28  tff('#skF_6', type, '#skF_6': $i).
% 6.06/2.28  tff('#skF_2', type, '#skF_2': $i).
% 6.06/2.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.06/2.28  tff('#skF_3', type, '#skF_3': $i).
% 6.06/2.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.06/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.06/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.06/2.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.06/2.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.06/2.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.06/2.28  tff('#skF_4', type, '#skF_4': $i).
% 6.06/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.06/2.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.06/2.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.06/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.06/2.28  
% 6.06/2.30  tff(f_132, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_2)).
% 6.06/2.30  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 6.06/2.30  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.06/2.30  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 6.06/2.30  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 6.06/2.30  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.06/2.30  tff(f_85, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.06/2.30  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.06/2.30  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.06/2.30  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.06/2.30  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 6.06/2.30  tff(f_36, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 6.06/2.30  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.06/2.30  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.06/2.30  tff(f_73, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.06/2.30  tff(c_52, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.06/2.30  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.06/2.30  tff(c_4222, plain, (![A_321, B_322, C_323, D_324]: (k8_relset_1(A_321, B_322, C_323, D_324)=k10_relat_1(C_323, D_324) | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.06/2.30  tff(c_4232, plain, (![D_324]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_324)=k10_relat_1('#skF_4', D_324))), inference(resolution, [status(thm)], [c_46, c_4222])).
% 6.06/2.30  tff(c_91, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.06/2.30  tff(c_104, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_91])).
% 6.06/2.30  tff(c_862, plain, (![A_136, B_137, C_138, D_139]: (k8_relset_1(A_136, B_137, C_138, D_139)=k10_relat_1(C_138, D_139) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.06/2.30  tff(c_872, plain, (![D_139]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_139)=k10_relat_1('#skF_4', D_139))), inference(resolution, [status(thm)], [c_46, c_862])).
% 6.06/2.30  tff(c_56, plain, (~r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')) | ~r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.06/2.30  tff(c_65, plain, (~r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_56])).
% 6.06/2.30  tff(c_62, plain, (r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.06/2.30  tff(c_106, plain, (r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_65, c_62])).
% 6.06/2.30  tff(c_876, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_872, c_106])).
% 6.06/2.30  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.06/2.30  tff(c_14, plain, (![C_13, A_11, B_12]: (r1_tarski(k9_relat_1(C_13, A_11), k9_relat_1(C_13, B_12)) | ~r1_tarski(A_11, B_12) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.06/2.30  tff(c_253, plain, (![B_93, A_94]: (r1_tarski(k9_relat_1(B_93, k10_relat_1(B_93, A_94)), A_94) | ~v1_funct_1(B_93) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.06/2.30  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.06/2.30  tff(c_2849, plain, (![A_244, A_245, B_246]: (r1_tarski(A_244, A_245) | ~r1_tarski(A_244, k9_relat_1(B_246, k10_relat_1(B_246, A_245))) | ~v1_funct_1(B_246) | ~v1_relat_1(B_246))), inference(resolution, [status(thm)], [c_253, c_2])).
% 6.06/2.30  tff(c_3358, plain, (![C_262, A_263, A_264]: (r1_tarski(k9_relat_1(C_262, A_263), A_264) | ~v1_funct_1(C_262) | ~r1_tarski(A_263, k10_relat_1(C_262, A_264)) | ~v1_relat_1(C_262))), inference(resolution, [status(thm)], [c_14, c_2849])).
% 6.06/2.30  tff(c_738, plain, (![A_124, B_125, C_126, D_127]: (k7_relset_1(A_124, B_125, C_126, D_127)=k9_relat_1(C_126, D_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.06/2.30  tff(c_748, plain, (![D_127]: (k7_relset_1('#skF_2', '#skF_3', '#skF_4', D_127)=k9_relat_1('#skF_4', D_127))), inference(resolution, [status(thm)], [c_46, c_738])).
% 6.06/2.30  tff(c_750, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_748, c_65])).
% 6.06/2.30  tff(c_3443, plain, (~v1_funct_1('#skF_4') | ~r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3358, c_750])).
% 6.06/2.30  tff(c_3506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_876, c_50, c_3443])).
% 6.06/2.30  tff(c_3507, plain, (~r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_56])).
% 6.06/2.30  tff(c_4234, plain, (~r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4232, c_3507])).
% 6.06/2.30  tff(c_3535, plain, (![C_272, A_273, B_274]: (v1_relat_1(C_272) | ~m1_subset_1(C_272, k1_zfmisc_1(k2_zfmisc_1(A_273, B_274))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.06/2.30  tff(c_3548, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_3535])).
% 6.06/2.30  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.06/2.30  tff(c_3511, plain, (![A_269, B_270]: (r1_tarski(A_269, B_270) | ~m1_subset_1(A_269, k1_zfmisc_1(B_270)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.06/2.30  tff(c_3532, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_3511])).
% 6.06/2.30  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.06/2.30  tff(c_3874, plain, (![A_301, B_302, C_303]: (k1_relset_1(A_301, B_302, C_303)=k1_relat_1(C_303) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.06/2.30  tff(c_3887, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_3874])).
% 6.06/2.30  tff(c_4807, plain, (![B_352, A_353, C_354]: (k1_xboole_0=B_352 | k1_relset_1(A_353, B_352, C_354)=A_353 | ~v1_funct_2(C_354, A_353, B_352) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(A_353, B_352))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.06/2.30  tff(c_4814, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_4807])).
% 6.06/2.30  tff(c_4822, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3887, c_4814])).
% 6.06/2.30  tff(c_4824, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_4822])).
% 6.06/2.30  tff(c_4352, plain, (![A_329, B_330, C_331, D_332]: (k7_relset_1(A_329, B_330, C_331, D_332)=k9_relat_1(C_331, D_332) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.06/2.30  tff(c_4362, plain, (![D_332]: (k7_relset_1('#skF_2', '#skF_3', '#skF_4', D_332)=k9_relat_1('#skF_4', D_332))), inference(resolution, [status(thm)], [c_46, c_4352])).
% 6.06/2.30  tff(c_3508, plain, (r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_56])).
% 6.06/2.30  tff(c_4370, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4362, c_3508])).
% 6.06/2.30  tff(c_5213, plain, (![A_376, C_377, B_378]: (r1_tarski(A_376, k10_relat_1(C_377, B_378)) | ~r1_tarski(k9_relat_1(C_377, A_376), B_378) | ~r1_tarski(A_376, k1_relat_1(C_377)) | ~v1_funct_1(C_377) | ~v1_relat_1(C_377))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.06/2.30  tff(c_5234, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4370, c_5213])).
% 6.06/2.30  tff(c_5259, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3548, c_50, c_3532, c_4824, c_5234])).
% 6.06/2.30  tff(c_5261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4234, c_5259])).
% 6.06/2.30  tff(c_5262, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4822])).
% 6.06/2.30  tff(c_6, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.06/2.30  tff(c_4, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.06/2.30  tff(c_3568, plain, (![A_280, B_281]: (r2_hidden(A_280, B_281) | v1_xboole_0(B_281) | ~m1_subset_1(A_280, B_281))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.06/2.30  tff(c_20, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.06/2.30  tff(c_3573, plain, (![B_282, A_283]: (~r1_tarski(B_282, A_283) | v1_xboole_0(B_282) | ~m1_subset_1(A_283, B_282))), inference(resolution, [status(thm)], [c_3568, c_20])).
% 6.06/2.30  tff(c_3597, plain, (![A_4]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_3573])).
% 6.06/2.30  tff(c_3601, plain, (![A_284]: (~m1_subset_1(A_284, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_3597])).
% 6.06/2.30  tff(c_3606, plain, $false, inference(resolution, [status(thm)], [c_6, c_3601])).
% 6.06/2.30  tff(c_3607, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_3597])).
% 6.06/2.30  tff(c_5278, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5262, c_3607])).
% 6.06/2.30  tff(c_5282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_5278])).
% 6.06/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.30  
% 6.06/2.30  Inference rules
% 6.06/2.30  ----------------------
% 6.06/2.30  #Ref     : 0
% 6.06/2.30  #Sup     : 1101
% 6.06/2.30  #Fact    : 0
% 6.06/2.30  #Define  : 0
% 6.06/2.30  #Split   : 33
% 6.06/2.30  #Chain   : 0
% 6.06/2.30  #Close   : 0
% 6.06/2.30  
% 6.06/2.30  Ordering : KBO
% 6.06/2.30  
% 6.06/2.30  Simplification rules
% 6.06/2.30  ----------------------
% 6.06/2.30  #Subsume      : 128
% 6.06/2.30  #Demod        : 406
% 6.06/2.30  #Tautology    : 317
% 6.06/2.30  #SimpNegUnit  : 4
% 6.06/2.30  #BackRed      : 45
% 6.06/2.30  
% 6.06/2.30  #Partial instantiations: 0
% 6.06/2.30  #Strategies tried      : 1
% 6.06/2.30  
% 6.06/2.30  Timing (in seconds)
% 6.06/2.30  ----------------------
% 6.06/2.30  Preprocessing        : 0.42
% 6.06/2.30  Parsing              : 0.21
% 6.06/2.30  CNF conversion       : 0.03
% 6.06/2.30  Main loop            : 1.05
% 6.06/2.30  Inferencing          : 0.36
% 6.06/2.30  Reduction            : 0.35
% 6.06/2.30  Demodulation         : 0.25
% 6.06/2.30  BG Simplification    : 0.04
% 6.06/2.30  Subsumption          : 0.20
% 6.06/2.30  Abstraction          : 0.06
% 6.06/2.30  MUC search           : 0.00
% 6.06/2.30  Cooper               : 0.00
% 6.06/2.30  Total                : 1.51
% 6.06/2.30  Index Insertion      : 0.00
% 6.06/2.30  Index Deletion       : 0.00
% 6.06/2.30  Index Matching       : 0.00
% 6.06/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
