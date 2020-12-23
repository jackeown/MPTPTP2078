%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:41 EST 2020

% Result     : Theorem 4.89s
% Output     : CNFRefutation 5.23s
% Verified   : 
% Statistics : Number of formulae       :  170 (1258 expanded)
%              Number of leaves         :   32 ( 419 expanded)
%              Depth                    :   16
%              Number of atoms          :  338 (3775 expanded)
%              Number of equality atoms :  144 (1042 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_149,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_158,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_149])).

tff(c_168,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_158])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_222,plain,(
    ! [A_66,B_67,D_68] :
      ( r2_relset_1(A_66,B_67,D_68,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_238,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_222])).

tff(c_242,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_265,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_242])).

tff(c_312,plain,(
    ! [B_89,A_90,C_91] :
      ( k1_xboole_0 = B_89
      | k1_relset_1(A_90,B_89,C_91) = A_90
      | ~ v1_funct_2(C_91,A_90,B_89)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_322,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_312])).

tff(c_339,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_265,c_322])).

tff(c_349,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_339])).

tff(c_155,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_149])).

tff(c_165,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_155])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_264,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_242])).

tff(c_319,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_312])).

tff(c_336,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_264,c_319])).

tff(c_343,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_613,plain,(
    ! [A_127,B_128] :
      ( r2_hidden('#skF_1'(A_127,B_128),k1_relat_1(A_127))
      | B_128 = A_127
      | k1_relat_1(B_128) != k1_relat_1(A_127)
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128)
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_621,plain,(
    ! [B_128] :
      ( r2_hidden('#skF_1'('#skF_4',B_128),'#skF_2')
      | B_128 = '#skF_4'
      | k1_relat_1(B_128) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_613])).

tff(c_635,plain,(
    ! [B_130] :
      ( r2_hidden('#skF_1'('#skF_4',B_130),'#skF_2')
      | B_130 = '#skF_4'
      | k1_relat_1(B_130) != '#skF_2'
      | ~ v1_funct_1(B_130)
      | ~ v1_relat_1(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_62,c_343,c_621])).

tff(c_50,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_642,plain,(
    ! [B_130] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_130)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_130))
      | B_130 = '#skF_4'
      | k1_relat_1(B_130) != '#skF_2'
      | ~ v1_funct_1(B_130)
      | ~ v1_relat_1(B_130) ) ),
    inference(resolution,[status(thm)],[c_635,c_50])).

tff(c_815,plain,(
    ! [B_145,A_146] :
      ( k1_funct_1(B_145,'#skF_1'(A_146,B_145)) != k1_funct_1(A_146,'#skF_1'(A_146,B_145))
      | B_145 = A_146
      | k1_relat_1(B_145) != k1_relat_1(A_146)
      | ~ v1_funct_1(B_145)
      | ~ v1_relat_1(B_145)
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_819,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_815])).

tff(c_822,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_56,c_349,c_165,c_62,c_349,c_343,c_819])).

tff(c_48,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_834,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_822,c_48])).

tff(c_845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_834])).

tff(c_846,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_101,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_101])).

tff(c_859,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_117])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_863,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_846,c_10])).

tff(c_116,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_101])).

tff(c_120,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_116,c_120])).

tff(c_205,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_884,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_205])).

tff(c_892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_859,c_884])).

tff(c_893,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_906,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_117])).

tff(c_910,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_893,c_10])).

tff(c_933,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_205])).

tff(c_941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_906,c_933])).

tff(c_942,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_948,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_52])).

tff(c_1088,plain,(
    ! [A_181,B_182,C_183] :
      ( k1_relset_1(A_181,B_182,C_183) = k1_relat_1(C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1150,plain,(
    ! [C_190] :
      ( k1_relset_1('#skF_2','#skF_3',C_190) = k1_relat_1(C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_1088])).

tff(c_1166,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_948,c_1150])).

tff(c_1278,plain,(
    ! [B_205,C_206,A_207] :
      ( k1_xboole_0 = B_205
      | v1_funct_2(C_206,A_207,B_205)
      | k1_relset_1(A_207,B_205,C_206) != A_207
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_207,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1281,plain,(
    ! [C_206] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(C_206,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',C_206) != '#skF_2'
      | ~ m1_subset_1(C_206,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_1278])).

tff(c_1374,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1281])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_953,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_8])).

tff(c_1006,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_953])).

tff(c_1395,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1374,c_1006])).

tff(c_1403,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1374,c_1374,c_10])).

tff(c_1455,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_942])).

tff(c_1457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1395,c_1455])).

tff(c_1459,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_1334,plain,(
    ! [B_214,A_215,C_216] :
      ( k1_xboole_0 = B_214
      | k1_relset_1(A_215,B_214,C_216) = A_215
      | ~ v1_funct_2(C_216,A_215,B_214)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_215,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1337,plain,(
    ! [C_216] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_216) = '#skF_2'
      | ~ v1_funct_2(C_216,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_216,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_1334])).

tff(c_1461,plain,(
    ! [C_224] :
      ( k1_relset_1('#skF_2','#skF_3',C_224) = '#skF_2'
      | ~ v1_funct_2(C_224,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_224,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1459,c_1337])).

tff(c_1467,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_948,c_1461])).

tff(c_1481,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1166,c_1467])).

tff(c_947,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_58])).

tff(c_1165,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_947,c_1150])).

tff(c_1464,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_947,c_1461])).

tff(c_1478,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1165,c_1464])).

tff(c_1710,plain,(
    ! [A_240,B_241] :
      ( r2_hidden('#skF_1'(A_240,B_241),k1_relat_1(A_240))
      | B_241 = A_240
      | k1_relat_1(B_241) != k1_relat_1(A_240)
      | ~ v1_funct_1(B_241)
      | ~ v1_relat_1(B_241)
      | ~ v1_funct_1(A_240)
      | ~ v1_relat_1(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1718,plain,(
    ! [B_241] :
      ( r2_hidden('#skF_1'('#skF_4',B_241),'#skF_2')
      | B_241 = '#skF_4'
      | k1_relat_1(B_241) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_241)
      | ~ v1_relat_1(B_241)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1478,c_1710])).

tff(c_1732,plain,(
    ! [B_243] :
      ( r2_hidden('#skF_1'('#skF_4',B_243),'#skF_2')
      | B_243 = '#skF_4'
      | k1_relat_1(B_243) != '#skF_2'
      | ~ v1_funct_1(B_243)
      | ~ v1_relat_1(B_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_62,c_1478,c_1718])).

tff(c_1739,plain,(
    ! [B_243] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_243)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_243))
      | B_243 = '#skF_4'
      | k1_relat_1(B_243) != '#skF_2'
      | ~ v1_funct_1(B_243)
      | ~ v1_relat_1(B_243) ) ),
    inference(resolution,[status(thm)],[c_1732,c_50])).

tff(c_2019,plain,(
    ! [B_256,A_257] :
      ( k1_funct_1(B_256,'#skF_1'(A_257,B_256)) != k1_funct_1(A_257,'#skF_1'(A_257,B_256))
      | B_256 = A_257
      | k1_relat_1(B_256) != k1_relat_1(A_257)
      | ~ v1_funct_1(B_256)
      | ~ v1_relat_1(B_256)
      | ~ v1_funct_1(A_257)
      | ~ v1_relat_1(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2023,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1739,c_2019])).

tff(c_2026,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_56,c_1481,c_165,c_62,c_1481,c_1478,c_2023])).

tff(c_115,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_101])).

tff(c_130,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_115,c_120])).

tff(c_204,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_944,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_204])).

tff(c_2047,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2026,c_944])).

tff(c_2060,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2047])).

tff(c_2062,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_953])).

tff(c_2066,plain,(
    ! [A_5] : r1_tarski('#skF_5',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2062,c_117])).

tff(c_2079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2066,c_944])).

tff(c_2080,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_2086,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_52])).

tff(c_2211,plain,(
    ! [A_285,B_286,C_287] :
      ( k1_relset_1(A_285,B_286,C_287) = k1_relat_1(C_287)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2259,plain,(
    ! [C_294] :
      ( k1_relset_1('#skF_2','#skF_3',C_294) = k1_relat_1(C_294)
      | ~ m1_subset_1(C_294,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2080,c_2211])).

tff(c_2275,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2086,c_2259])).

tff(c_2465,plain,(
    ! [B_319,A_320,C_321] :
      ( k1_xboole_0 = B_319
      | k1_relset_1(A_320,B_319,C_321) = A_320
      | ~ v1_funct_2(C_321,A_320,B_319)
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(A_320,B_319))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2468,plain,(
    ! [C_321] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_321) = '#skF_2'
      | ~ v1_funct_2(C_321,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_321,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2080,c_2465])).

tff(c_2513,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2468])).

tff(c_2091,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2080,c_8])).

tff(c_2147,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2091])).

tff(c_2533,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2513,c_2147])).

tff(c_2656,plain,(
    ! [A_333] : k2_zfmisc_1(A_333,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2513,c_2513,c_10])).

tff(c_2682,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2656,c_2080])).

tff(c_2698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2533,c_2682])).

tff(c_2775,plain,(
    ! [C_340] :
      ( k1_relset_1('#skF_2','#skF_3',C_340) = '#skF_2'
      | ~ v1_funct_2(C_340,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_340,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_2468])).

tff(c_2781,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2086,c_2775])).

tff(c_2795,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2275,c_2781])).

tff(c_2085,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_58])).

tff(c_2274,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2085,c_2259])).

tff(c_2778,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2085,c_2775])).

tff(c_2792,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2274,c_2778])).

tff(c_2829,plain,(
    ! [A_341,B_342] :
      ( r2_hidden('#skF_1'(A_341,B_342),k1_relat_1(A_341))
      | B_342 = A_341
      | k1_relat_1(B_342) != k1_relat_1(A_341)
      | ~ v1_funct_1(B_342)
      | ~ v1_relat_1(B_342)
      | ~ v1_funct_1(A_341)
      | ~ v1_relat_1(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2837,plain,(
    ! [B_342] :
      ( r2_hidden('#skF_1'('#skF_4',B_342),'#skF_2')
      | B_342 = '#skF_4'
      | k1_relat_1(B_342) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_342)
      | ~ v1_relat_1(B_342)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2792,c_2829])).

tff(c_2868,plain,(
    ! [B_344] :
      ( r2_hidden('#skF_1'('#skF_4',B_344),'#skF_2')
      | B_344 = '#skF_4'
      | k1_relat_1(B_344) != '#skF_2'
      | ~ v1_funct_1(B_344)
      | ~ v1_relat_1(B_344) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_62,c_2792,c_2837])).

tff(c_2875,plain,(
    ! [B_344] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_344)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_344))
      | B_344 = '#skF_4'
      | k1_relat_1(B_344) != '#skF_2'
      | ~ v1_funct_1(B_344)
      | ~ v1_relat_1(B_344) ) ),
    inference(resolution,[status(thm)],[c_2868,c_50])).

tff(c_3019,plain,(
    ! [B_358,A_359] :
      ( k1_funct_1(B_358,'#skF_1'(A_359,B_358)) != k1_funct_1(A_359,'#skF_1'(A_359,B_358))
      | B_358 = A_359
      | k1_relat_1(B_358) != k1_relat_1(A_359)
      | ~ v1_funct_1(B_358)
      | ~ v1_relat_1(B_358)
      | ~ v1_funct_1(A_359)
      | ~ v1_relat_1(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3023,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2875,c_3019])).

tff(c_3026,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_56,c_2795,c_165,c_62,c_2795,c_2792,c_3023])).

tff(c_2082,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_2143,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_2082])).

tff(c_3033,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3026,c_2143])).

tff(c_3046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3033])).

tff(c_3048,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2091])).

tff(c_3052,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3048,c_117])).

tff(c_3065,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3052,c_2143])).

tff(c_3066,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_3114,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_3066])).

tff(c_3119,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3114,c_48])).

tff(c_3070,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_58])).

tff(c_3149,plain,(
    ! [A_369,B_370,D_371] :
      ( r2_relset_1(A_369,B_370,D_371,D_371)
      | ~ m1_subset_1(D_371,k1_zfmisc_1(k2_zfmisc_1(A_369,B_370))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3183,plain,(
    ! [D_380] :
      ( r2_relset_1('#skF_2','#skF_3',D_380,D_380)
      | ~ m1_subset_1(D_380,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2080,c_3149])).

tff(c_3185,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_3070,c_3183])).

tff(c_3195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3119,c_3185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:58:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.89/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.96  
% 4.89/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.96  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.89/1.96  
% 4.89/1.96  %Foreground sorts:
% 4.89/1.96  
% 4.89/1.96  
% 4.89/1.96  %Background operators:
% 4.89/1.96  
% 4.89/1.96  
% 4.89/1.96  %Foreground operators:
% 4.89/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.89/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.89/1.96  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.89/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.89/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.89/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.89/1.96  tff('#skF_5', type, '#skF_5': $i).
% 4.89/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.89/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.89/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.89/1.96  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.89/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.89/1.96  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.89/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.89/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.89/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.89/1.96  tff('#skF_4', type, '#skF_4': $i).
% 4.89/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.89/1.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.89/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.89/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.89/1.96  
% 5.23/1.99  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.23/1.99  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.23/1.99  tff(f_127, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 5.23/1.99  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.23/1.99  tff(f_88, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.23/1.99  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.23/1.99  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.23/1.99  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 5.23/1.99  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.23/1.99  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.23/1.99  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.23/1.99  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.23/1.99  tff(c_24, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.23/1.99  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.23/1.99  tff(c_149, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.23/1.99  tff(c_158, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_149])).
% 5.23/1.99  tff(c_168, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_158])).
% 5.23/1.99  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.23/1.99  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.23/1.99  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.23/1.99  tff(c_222, plain, (![A_66, B_67, D_68]: (r2_relset_1(A_66, B_67, D_68, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.23/1.99  tff(c_238, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_222])).
% 5.23/1.99  tff(c_242, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.23/1.99  tff(c_265, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_242])).
% 5.23/1.99  tff(c_312, plain, (![B_89, A_90, C_91]: (k1_xboole_0=B_89 | k1_relset_1(A_90, B_89, C_91)=A_90 | ~v1_funct_2(C_91, A_90, B_89) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.23/1.99  tff(c_322, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_312])).
% 5.23/1.99  tff(c_339, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_265, c_322])).
% 5.23/1.99  tff(c_349, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_339])).
% 5.23/1.99  tff(c_155, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_149])).
% 5.23/1.99  tff(c_165, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_155])).
% 5.23/1.99  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.23/1.99  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.23/1.99  tff(c_264, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_242])).
% 5.23/1.99  tff(c_319, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_312])).
% 5.23/1.99  tff(c_336, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_264, c_319])).
% 5.23/1.99  tff(c_343, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_336])).
% 5.23/1.99  tff(c_613, plain, (![A_127, B_128]: (r2_hidden('#skF_1'(A_127, B_128), k1_relat_1(A_127)) | B_128=A_127 | k1_relat_1(B_128)!=k1_relat_1(A_127) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.23/1.99  tff(c_621, plain, (![B_128]: (r2_hidden('#skF_1'('#skF_4', B_128), '#skF_2') | B_128='#skF_4' | k1_relat_1(B_128)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_128) | ~v1_relat_1(B_128) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_343, c_613])).
% 5.23/1.99  tff(c_635, plain, (![B_130]: (r2_hidden('#skF_1'('#skF_4', B_130), '#skF_2') | B_130='#skF_4' | k1_relat_1(B_130)!='#skF_2' | ~v1_funct_1(B_130) | ~v1_relat_1(B_130))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_62, c_343, c_621])).
% 5.23/1.99  tff(c_50, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.23/1.99  tff(c_642, plain, (![B_130]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_130))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_130)) | B_130='#skF_4' | k1_relat_1(B_130)!='#skF_2' | ~v1_funct_1(B_130) | ~v1_relat_1(B_130))), inference(resolution, [status(thm)], [c_635, c_50])).
% 5.23/1.99  tff(c_815, plain, (![B_145, A_146]: (k1_funct_1(B_145, '#skF_1'(A_146, B_145))!=k1_funct_1(A_146, '#skF_1'(A_146, B_145)) | B_145=A_146 | k1_relat_1(B_145)!=k1_relat_1(A_146) | ~v1_funct_1(B_145) | ~v1_relat_1(B_145) | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.23/1.99  tff(c_819, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_642, c_815])).
% 5.23/1.99  tff(c_822, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_56, c_349, c_165, c_62, c_349, c_343, c_819])).
% 5.23/1.99  tff(c_48, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.23/1.99  tff(c_834, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_822, c_48])).
% 5.23/1.99  tff(c_845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_238, c_834])).
% 5.23/1.99  tff(c_846, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_339])).
% 5.23/1.99  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.23/1.99  tff(c_101, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.23/1.99  tff(c_117, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_101])).
% 5.23/1.99  tff(c_859, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_846, c_117])).
% 5.23/1.99  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.23/1.99  tff(c_863, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_846, c_846, c_10])).
% 5.23/1.99  tff(c_116, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_101])).
% 5.23/1.99  tff(c_120, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.23/1.99  tff(c_129, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_116, c_120])).
% 5.23/1.99  tff(c_205, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_129])).
% 5.23/1.99  tff(c_884, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_863, c_205])).
% 5.23/1.99  tff(c_892, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_859, c_884])).
% 5.23/1.99  tff(c_893, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_336])).
% 5.23/1.99  tff(c_906, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_893, c_117])).
% 5.23/1.99  tff(c_910, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_893, c_893, c_10])).
% 5.23/1.99  tff(c_933, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_910, c_205])).
% 5.23/1.99  tff(c_941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_906, c_933])).
% 5.23/1.99  tff(c_942, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_129])).
% 5.23/1.99  tff(c_948, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_942, c_52])).
% 5.23/1.99  tff(c_1088, plain, (![A_181, B_182, C_183]: (k1_relset_1(A_181, B_182, C_183)=k1_relat_1(C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.23/1.99  tff(c_1150, plain, (![C_190]: (k1_relset_1('#skF_2', '#skF_3', C_190)=k1_relat_1(C_190) | ~m1_subset_1(C_190, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_942, c_1088])).
% 5.23/1.99  tff(c_1166, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_948, c_1150])).
% 5.23/1.99  tff(c_1278, plain, (![B_205, C_206, A_207]: (k1_xboole_0=B_205 | v1_funct_2(C_206, A_207, B_205) | k1_relset_1(A_207, B_205, C_206)!=A_207 | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_207, B_205))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.23/1.99  tff(c_1281, plain, (![C_206]: (k1_xboole_0='#skF_3' | v1_funct_2(C_206, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', C_206)!='#skF_2' | ~m1_subset_1(C_206, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_942, c_1278])).
% 5.23/1.99  tff(c_1374, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1281])).
% 5.23/1.99  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.23/1.99  tff(c_953, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_942, c_8])).
% 5.23/1.99  tff(c_1006, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_953])).
% 5.23/1.99  tff(c_1395, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1374, c_1006])).
% 5.23/1.99  tff(c_1403, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1374, c_1374, c_10])).
% 5.23/1.99  tff(c_1455, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_942])).
% 5.23/1.99  tff(c_1457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1395, c_1455])).
% 5.23/1.99  tff(c_1459, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1281])).
% 5.23/1.99  tff(c_1334, plain, (![B_214, A_215, C_216]: (k1_xboole_0=B_214 | k1_relset_1(A_215, B_214, C_216)=A_215 | ~v1_funct_2(C_216, A_215, B_214) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_215, B_214))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.23/1.99  tff(c_1337, plain, (![C_216]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_216)='#skF_2' | ~v1_funct_2(C_216, '#skF_2', '#skF_3') | ~m1_subset_1(C_216, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_942, c_1334])).
% 5.23/1.99  tff(c_1461, plain, (![C_224]: (k1_relset_1('#skF_2', '#skF_3', C_224)='#skF_2' | ~v1_funct_2(C_224, '#skF_2', '#skF_3') | ~m1_subset_1(C_224, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_1459, c_1337])).
% 5.23/1.99  tff(c_1467, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_948, c_1461])).
% 5.23/1.99  tff(c_1481, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1166, c_1467])).
% 5.23/1.99  tff(c_947, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_942, c_58])).
% 5.23/1.99  tff(c_1165, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_947, c_1150])).
% 5.23/1.99  tff(c_1464, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_947, c_1461])).
% 5.23/1.99  tff(c_1478, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1165, c_1464])).
% 5.23/1.99  tff(c_1710, plain, (![A_240, B_241]: (r2_hidden('#skF_1'(A_240, B_241), k1_relat_1(A_240)) | B_241=A_240 | k1_relat_1(B_241)!=k1_relat_1(A_240) | ~v1_funct_1(B_241) | ~v1_relat_1(B_241) | ~v1_funct_1(A_240) | ~v1_relat_1(A_240))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.23/1.99  tff(c_1718, plain, (![B_241]: (r2_hidden('#skF_1'('#skF_4', B_241), '#skF_2') | B_241='#skF_4' | k1_relat_1(B_241)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_241) | ~v1_relat_1(B_241) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1478, c_1710])).
% 5.23/1.99  tff(c_1732, plain, (![B_243]: (r2_hidden('#skF_1'('#skF_4', B_243), '#skF_2') | B_243='#skF_4' | k1_relat_1(B_243)!='#skF_2' | ~v1_funct_1(B_243) | ~v1_relat_1(B_243))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_62, c_1478, c_1718])).
% 5.23/1.99  tff(c_1739, plain, (![B_243]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_243))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_243)) | B_243='#skF_4' | k1_relat_1(B_243)!='#skF_2' | ~v1_funct_1(B_243) | ~v1_relat_1(B_243))), inference(resolution, [status(thm)], [c_1732, c_50])).
% 5.23/1.99  tff(c_2019, plain, (![B_256, A_257]: (k1_funct_1(B_256, '#skF_1'(A_257, B_256))!=k1_funct_1(A_257, '#skF_1'(A_257, B_256)) | B_256=A_257 | k1_relat_1(B_256)!=k1_relat_1(A_257) | ~v1_funct_1(B_256) | ~v1_relat_1(B_256) | ~v1_funct_1(A_257) | ~v1_relat_1(A_257))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.23/1.99  tff(c_2023, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1739, c_2019])).
% 5.23/1.99  tff(c_2026, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_56, c_1481, c_165, c_62, c_1481, c_1478, c_2023])).
% 5.23/1.99  tff(c_115, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_101])).
% 5.23/1.99  tff(c_130, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_115, c_120])).
% 5.23/1.99  tff(c_204, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_130])).
% 5.23/1.99  tff(c_944, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_942, c_204])).
% 5.23/1.99  tff(c_2047, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2026, c_944])).
% 5.23/1.99  tff(c_2060, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2047])).
% 5.23/1.99  tff(c_2062, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_953])).
% 5.23/1.99  tff(c_2066, plain, (![A_5]: (r1_tarski('#skF_5', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2062, c_117])).
% 5.23/1.99  tff(c_2079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2066, c_944])).
% 5.23/1.99  tff(c_2080, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_130])).
% 5.23/1.99  tff(c_2086, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_52])).
% 5.23/1.99  tff(c_2211, plain, (![A_285, B_286, C_287]: (k1_relset_1(A_285, B_286, C_287)=k1_relat_1(C_287) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.23/1.99  tff(c_2259, plain, (![C_294]: (k1_relset_1('#skF_2', '#skF_3', C_294)=k1_relat_1(C_294) | ~m1_subset_1(C_294, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2080, c_2211])).
% 5.23/1.99  tff(c_2275, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2086, c_2259])).
% 5.23/1.99  tff(c_2465, plain, (![B_319, A_320, C_321]: (k1_xboole_0=B_319 | k1_relset_1(A_320, B_319, C_321)=A_320 | ~v1_funct_2(C_321, A_320, B_319) | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(A_320, B_319))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.23/1.99  tff(c_2468, plain, (![C_321]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_321)='#skF_2' | ~v1_funct_2(C_321, '#skF_2', '#skF_3') | ~m1_subset_1(C_321, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2080, c_2465])).
% 5.23/1.99  tff(c_2513, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2468])).
% 5.23/1.99  tff(c_2091, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2080, c_8])).
% 5.23/1.99  tff(c_2147, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_2091])).
% 5.23/1.99  tff(c_2533, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2513, c_2147])).
% 5.23/1.99  tff(c_2656, plain, (![A_333]: (k2_zfmisc_1(A_333, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2513, c_2513, c_10])).
% 5.23/1.99  tff(c_2682, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2656, c_2080])).
% 5.23/1.99  tff(c_2698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2533, c_2682])).
% 5.23/1.99  tff(c_2775, plain, (![C_340]: (k1_relset_1('#skF_2', '#skF_3', C_340)='#skF_2' | ~v1_funct_2(C_340, '#skF_2', '#skF_3') | ~m1_subset_1(C_340, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_2468])).
% 5.23/1.99  tff(c_2781, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2086, c_2775])).
% 5.23/1.99  tff(c_2795, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2275, c_2781])).
% 5.23/1.99  tff(c_2085, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_58])).
% 5.23/1.99  tff(c_2274, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2085, c_2259])).
% 5.23/1.99  tff(c_2778, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2085, c_2775])).
% 5.23/1.99  tff(c_2792, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2274, c_2778])).
% 5.23/1.99  tff(c_2829, plain, (![A_341, B_342]: (r2_hidden('#skF_1'(A_341, B_342), k1_relat_1(A_341)) | B_342=A_341 | k1_relat_1(B_342)!=k1_relat_1(A_341) | ~v1_funct_1(B_342) | ~v1_relat_1(B_342) | ~v1_funct_1(A_341) | ~v1_relat_1(A_341))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.23/1.99  tff(c_2837, plain, (![B_342]: (r2_hidden('#skF_1'('#skF_4', B_342), '#skF_2') | B_342='#skF_4' | k1_relat_1(B_342)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_342) | ~v1_relat_1(B_342) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2792, c_2829])).
% 5.23/1.99  tff(c_2868, plain, (![B_344]: (r2_hidden('#skF_1'('#skF_4', B_344), '#skF_2') | B_344='#skF_4' | k1_relat_1(B_344)!='#skF_2' | ~v1_funct_1(B_344) | ~v1_relat_1(B_344))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_62, c_2792, c_2837])).
% 5.23/1.99  tff(c_2875, plain, (![B_344]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_344))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_344)) | B_344='#skF_4' | k1_relat_1(B_344)!='#skF_2' | ~v1_funct_1(B_344) | ~v1_relat_1(B_344))), inference(resolution, [status(thm)], [c_2868, c_50])).
% 5.23/1.99  tff(c_3019, plain, (![B_358, A_359]: (k1_funct_1(B_358, '#skF_1'(A_359, B_358))!=k1_funct_1(A_359, '#skF_1'(A_359, B_358)) | B_358=A_359 | k1_relat_1(B_358)!=k1_relat_1(A_359) | ~v1_funct_1(B_358) | ~v1_relat_1(B_358) | ~v1_funct_1(A_359) | ~v1_relat_1(A_359))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.23/1.99  tff(c_3023, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2875, c_3019])).
% 5.23/1.99  tff(c_3026, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_56, c_2795, c_165, c_62, c_2795, c_2792, c_3023])).
% 5.23/1.99  tff(c_2082, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_129])).
% 5.23/1.99  tff(c_2143, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_2082])).
% 5.23/1.99  tff(c_3033, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3026, c_2143])).
% 5.23/1.99  tff(c_3046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3033])).
% 5.23/1.99  tff(c_3048, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2091])).
% 5.23/1.99  tff(c_3052, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_3048, c_117])).
% 5.23/1.99  tff(c_3065, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3052, c_2143])).
% 5.23/1.99  tff(c_3066, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_129])).
% 5.23/1.99  tff(c_3114, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_3066])).
% 5.23/1.99  tff(c_3119, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3114, c_48])).
% 5.23/1.99  tff(c_3070, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_58])).
% 5.23/1.99  tff(c_3149, plain, (![A_369, B_370, D_371]: (r2_relset_1(A_369, B_370, D_371, D_371) | ~m1_subset_1(D_371, k1_zfmisc_1(k2_zfmisc_1(A_369, B_370))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.23/1.99  tff(c_3183, plain, (![D_380]: (r2_relset_1('#skF_2', '#skF_3', D_380, D_380) | ~m1_subset_1(D_380, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2080, c_3149])).
% 5.23/1.99  tff(c_3185, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_3070, c_3183])).
% 5.23/1.99  tff(c_3195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3119, c_3185])).
% 5.23/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/1.99  
% 5.23/1.99  Inference rules
% 5.23/1.99  ----------------------
% 5.23/1.99  #Ref     : 3
% 5.23/1.99  #Sup     : 612
% 5.23/1.99  #Fact    : 0
% 5.23/1.99  #Define  : 0
% 5.23/1.99  #Split   : 18
% 5.23/1.99  #Chain   : 0
% 5.23/1.99  #Close   : 0
% 5.23/1.99  
% 5.23/1.99  Ordering : KBO
% 5.23/1.99  
% 5.23/1.99  Simplification rules
% 5.23/1.99  ----------------------
% 5.23/1.99  #Subsume      : 82
% 5.23/1.99  #Demod        : 804
% 5.23/1.99  #Tautology    : 328
% 5.23/1.99  #SimpNegUnit  : 42
% 5.23/1.99  #BackRed      : 204
% 5.23/1.99  
% 5.23/1.99  #Partial instantiations: 0
% 5.23/1.99  #Strategies tried      : 1
% 5.23/1.99  
% 5.23/1.99  Timing (in seconds)
% 5.23/1.99  ----------------------
% 5.23/1.99  Preprocessing        : 0.36
% 5.23/1.99  Parsing              : 0.19
% 5.23/1.99  CNF conversion       : 0.03
% 5.23/1.99  Main loop            : 0.78
% 5.23/1.99  Inferencing          : 0.27
% 5.23/1.99  Reduction            : 0.26
% 5.23/1.99  Demodulation         : 0.19
% 5.23/1.99  BG Simplification    : 0.03
% 5.23/1.99  Subsumption          : 0.15
% 5.23/1.99  Abstraction          : 0.03
% 5.23/1.99  MUC search           : 0.00
% 5.23/1.99  Cooper               : 0.00
% 5.23/1.99  Total                : 1.19
% 5.23/1.99  Index Insertion      : 0.00
% 5.23/1.99  Index Deletion       : 0.00
% 5.23/1.99  Index Matching       : 0.00
% 5.23/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
