%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:20 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 454 expanded)
%              Number of leaves         :   36 ( 168 expanded)
%              Depth                    :   15
%              Number of atoms          :  177 (1238 expanded)
%              Number of equality atoms :   38 ( 223 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ! [C] :
                  ( m1_subset_1(C,A)
                 => k3_funct_2(A,A,B,C) = C )
             => r2_funct_2(A,A,B,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_99,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_60,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_64,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_60])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_65,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_69,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_65])).

tff(c_83,plain,(
    ! [B_58,A_59] :
      ( k1_relat_1(B_58) = A_59
      | ~ v1_partfun1(B_58,A_59)
      | ~ v4_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_86,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_69,c_83])).

tff(c_89,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_86])).

tff(c_90,plain,(
    ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_42,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_185,plain,(
    ! [C_87,A_88,B_89] :
      ( v1_partfun1(C_87,A_88)
      | ~ v1_funct_2(C_87,A_88,B_89)
      | ~ v1_funct_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | v1_xboole_0(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_192,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_185])).

tff(c_196,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_192])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_90,c_196])).

tff(c_199,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_32,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6,plain,(
    ! [B_5] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_5),B_5),k1_relat_1(B_5))
      | k6_relat_1(k1_relat_1(B_5)) = B_5
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_255,plain,(
    ! [B_99] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_99),B_99),k1_relat_1(B_99))
      | k6_partfun1(k1_relat_1(B_99)) = B_99
      | ~ v1_funct_1(B_99)
      | ~ v1_relat_1(B_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_258,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_255])).

tff(c_263,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_44,c_199,c_199,c_258])).

tff(c_279,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_36,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_280,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_36])).

tff(c_350,plain,(
    ! [A_144,B_145,C_146,D_147] :
      ( r2_funct_2(A_144,B_145,C_146,C_146)
      | ~ m1_subset_1(D_147,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_funct_2(D_147,A_144,B_145)
      | ~ v1_funct_1(D_147)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_funct_2(C_146,A_144,B_145)
      | ~ v1_funct_1(C_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_355,plain,(
    ! [C_146] :
      ( r2_funct_2('#skF_2','#skF_2',C_146,C_146)
      | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_146,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_146) ) ),
    inference(resolution,[status(thm)],[c_40,c_350])).

tff(c_360,plain,(
    ! [C_148] :
      ( r2_funct_2('#skF_2','#skF_2',C_148,C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_148,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_355])).

tff(c_365,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_360])).

tff(c_369,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_365])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_369])).

tff(c_373,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_4,plain,(
    ! [B_5] :
      ( k1_funct_1(B_5,'#skF_1'(k1_relat_1(B_5),B_5)) != '#skF_1'(k1_relat_1(B_5),B_5)
      | k6_relat_1(k1_relat_1(B_5)) = B_5
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_404,plain,(
    ! [B_161] :
      ( k1_funct_1(B_161,'#skF_1'(k1_relat_1(B_161),B_161)) != '#skF_1'(k1_relat_1(B_161),B_161)
      | k6_partfun1(k1_relat_1(B_161)) = B_161
      | ~ v1_funct_1(B_161)
      | ~ v1_relat_1(B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4])).

tff(c_407,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_404])).

tff(c_409,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_44,c_199,c_199,c_407])).

tff(c_410,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_373,c_409])).

tff(c_372,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_201,plain,(
    ! [A_90,B_91,C_92] :
      ( k1_relset_1(A_90,B_91,C_92) = k1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_205,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_201])).

tff(c_216,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_205])).

tff(c_221,plain,(
    ! [A_93,B_94,C_95] :
      ( m1_subset_1(k1_relset_1(A_93,B_94,C_95),k1_zfmisc_1(A_93))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_242,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_221])).

tff(c_249,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_242])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_252,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_2')
      | ~ r2_hidden(A_1,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_249,c_2])).

tff(c_377,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_372,c_252])).

tff(c_38,plain,(
    ! [C_40] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_40) = C_40
      | ~ m1_subset_1(C_40,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_381,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_377,c_38])).

tff(c_421,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( k3_funct_2(A_170,B_171,C_172,D_173) = k1_funct_1(C_172,D_173)
      | ~ m1_subset_1(D_173,A_170)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171)))
      | ~ v1_funct_2(C_172,A_170,B_171)
      | ~ v1_funct_1(C_172)
      | v1_xboole_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_423,plain,(
    ! [B_171,C_172] :
      ( k3_funct_2('#skF_2',B_171,C_172,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_172,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_171)))
      | ~ v1_funct_2(C_172,'#skF_2',B_171)
      | ~ v1_funct_1(C_172)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_377,c_421])).

tff(c_440,plain,(
    ! [B_179,C_180] :
      ( k3_funct_2('#skF_2',B_179,C_180,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_180,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_179)))
      | ~ v1_funct_2(C_180,'#skF_2',B_179)
      | ~ v1_funct_1(C_180) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_423])).

tff(c_447,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_440])).

tff(c_451,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_381,c_447])).

tff(c_453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_410,c_451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.42  
% 2.73/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.42  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.73/1.42  
% 2.73/1.42  %Foreground sorts:
% 2.73/1.42  
% 2.73/1.42  
% 2.73/1.42  %Background operators:
% 2.73/1.42  
% 2.73/1.42  
% 2.73/1.42  %Foreground operators:
% 2.73/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.42  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.73/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.73/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.73/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.73/1.42  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.73/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.42  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.73/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.42  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.73/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.42  
% 2.98/1.44  tff(f_131, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t201_funct_2)).
% 2.98/1.44  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.98/1.44  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.98/1.44  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 2.98/1.44  tff(f_76, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.98/1.44  tff(f_99, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.98/1.44  tff(f_44, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.98/1.44  tff(f_113, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 2.98/1.44  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.98/1.44  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.98/1.44  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.98/1.44  tff(f_97, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.98/1.44  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.98/1.44  tff(c_60, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.98/1.44  tff(c_64, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_60])).
% 2.98/1.44  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.98/1.44  tff(c_46, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.98/1.44  tff(c_65, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.98/1.44  tff(c_69, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_65])).
% 2.98/1.44  tff(c_83, plain, (![B_58, A_59]: (k1_relat_1(B_58)=A_59 | ~v1_partfun1(B_58, A_59) | ~v4_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.98/1.44  tff(c_86, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_69, c_83])).
% 2.98/1.44  tff(c_89, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_86])).
% 2.98/1.44  tff(c_90, plain, (~v1_partfun1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_89])).
% 2.98/1.44  tff(c_42, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.98/1.44  tff(c_185, plain, (![C_87, A_88, B_89]: (v1_partfun1(C_87, A_88) | ~v1_funct_2(C_87, A_88, B_89) | ~v1_funct_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | v1_xboole_0(B_89))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.98/1.44  tff(c_192, plain, (v1_partfun1('#skF_3', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_185])).
% 2.98/1.44  tff(c_196, plain, (v1_partfun1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_192])).
% 2.98/1.44  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_90, c_196])).
% 2.98/1.44  tff(c_199, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_89])).
% 2.98/1.44  tff(c_32, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.98/1.44  tff(c_6, plain, (![B_5]: (r2_hidden('#skF_1'(k1_relat_1(B_5), B_5), k1_relat_1(B_5)) | k6_relat_1(k1_relat_1(B_5))=B_5 | ~v1_funct_1(B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.98/1.44  tff(c_255, plain, (![B_99]: (r2_hidden('#skF_1'(k1_relat_1(B_99), B_99), k1_relat_1(B_99)) | k6_partfun1(k1_relat_1(B_99))=B_99 | ~v1_funct_1(B_99) | ~v1_relat_1(B_99))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6])).
% 2.98/1.44  tff(c_258, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_199, c_255])).
% 2.98/1.44  tff(c_263, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_44, c_199, c_199, c_258])).
% 2.98/1.44  tff(c_279, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_263])).
% 2.98/1.44  tff(c_36, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.98/1.44  tff(c_280, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_36])).
% 2.98/1.44  tff(c_350, plain, (![A_144, B_145, C_146, D_147]: (r2_funct_2(A_144, B_145, C_146, C_146) | ~m1_subset_1(D_147, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_funct_2(D_147, A_144, B_145) | ~v1_funct_1(D_147) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_funct_2(C_146, A_144, B_145) | ~v1_funct_1(C_146))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.98/1.44  tff(c_355, plain, (![C_146]: (r2_funct_2('#skF_2', '#skF_2', C_146, C_146) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(C_146, '#skF_2', '#skF_2') | ~v1_funct_1(C_146))), inference(resolution, [status(thm)], [c_40, c_350])).
% 2.98/1.44  tff(c_360, plain, (![C_148]: (r2_funct_2('#skF_2', '#skF_2', C_148, C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(C_148, '#skF_2', '#skF_2') | ~v1_funct_1(C_148))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_355])).
% 2.98/1.44  tff(c_365, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_360])).
% 2.98/1.44  tff(c_369, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_365])).
% 2.98/1.44  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_280, c_369])).
% 2.98/1.44  tff(c_373, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_263])).
% 2.98/1.44  tff(c_4, plain, (![B_5]: (k1_funct_1(B_5, '#skF_1'(k1_relat_1(B_5), B_5))!='#skF_1'(k1_relat_1(B_5), B_5) | k6_relat_1(k1_relat_1(B_5))=B_5 | ~v1_funct_1(B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.98/1.44  tff(c_404, plain, (![B_161]: (k1_funct_1(B_161, '#skF_1'(k1_relat_1(B_161), B_161))!='#skF_1'(k1_relat_1(B_161), B_161) | k6_partfun1(k1_relat_1(B_161))=B_161 | ~v1_funct_1(B_161) | ~v1_relat_1(B_161))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4])).
% 2.98/1.44  tff(c_407, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_199, c_404])).
% 2.98/1.44  tff(c_409, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_44, c_199, c_199, c_407])).
% 2.98/1.44  tff(c_410, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_373, c_409])).
% 2.98/1.44  tff(c_372, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_263])).
% 2.98/1.44  tff(c_201, plain, (![A_90, B_91, C_92]: (k1_relset_1(A_90, B_91, C_92)=k1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.98/1.44  tff(c_205, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_201])).
% 2.98/1.44  tff(c_216, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_199, c_205])).
% 2.98/1.44  tff(c_221, plain, (![A_93, B_94, C_95]: (m1_subset_1(k1_relset_1(A_93, B_94, C_95), k1_zfmisc_1(A_93)) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.98/1.44  tff(c_242, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_216, c_221])).
% 2.98/1.44  tff(c_249, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_242])).
% 2.98/1.44  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.98/1.44  tff(c_252, plain, (![A_1]: (m1_subset_1(A_1, '#skF_2') | ~r2_hidden(A_1, '#skF_2'))), inference(resolution, [status(thm)], [c_249, c_2])).
% 2.98/1.44  tff(c_377, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_372, c_252])).
% 2.98/1.44  tff(c_38, plain, (![C_40]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_40)=C_40 | ~m1_subset_1(C_40, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.98/1.44  tff(c_381, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_377, c_38])).
% 2.98/1.44  tff(c_421, plain, (![A_170, B_171, C_172, D_173]: (k3_funct_2(A_170, B_171, C_172, D_173)=k1_funct_1(C_172, D_173) | ~m1_subset_1(D_173, A_170) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))) | ~v1_funct_2(C_172, A_170, B_171) | ~v1_funct_1(C_172) | v1_xboole_0(A_170))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.98/1.44  tff(c_423, plain, (![B_171, C_172]: (k3_funct_2('#skF_2', B_171, C_172, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_172, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_171))) | ~v1_funct_2(C_172, '#skF_2', B_171) | ~v1_funct_1(C_172) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_377, c_421])).
% 2.98/1.44  tff(c_440, plain, (![B_179, C_180]: (k3_funct_2('#skF_2', B_179, C_180, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_180, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_179))) | ~v1_funct_2(C_180, '#skF_2', B_179) | ~v1_funct_1(C_180))), inference(negUnitSimplification, [status(thm)], [c_46, c_423])).
% 2.98/1.44  tff(c_447, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_440])).
% 2.98/1.44  tff(c_451, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_381, c_447])).
% 2.98/1.44  tff(c_453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_410, c_451])).
% 2.98/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.44  
% 2.98/1.44  Inference rules
% 2.98/1.44  ----------------------
% 2.98/1.44  #Ref     : 0
% 2.98/1.44  #Sup     : 82
% 2.98/1.44  #Fact    : 0
% 2.98/1.44  #Define  : 0
% 2.98/1.44  #Split   : 5
% 2.98/1.44  #Chain   : 0
% 2.98/1.44  #Close   : 0
% 2.98/1.44  
% 2.98/1.44  Ordering : KBO
% 2.98/1.44  
% 2.98/1.44  Simplification rules
% 2.98/1.44  ----------------------
% 2.98/1.44  #Subsume      : 3
% 2.98/1.44  #Demod        : 73
% 2.98/1.44  #Tautology    : 23
% 2.98/1.44  #SimpNegUnit  : 7
% 2.98/1.44  #BackRed      : 1
% 2.98/1.44  
% 2.98/1.44  #Partial instantiations: 0
% 2.98/1.44  #Strategies tried      : 1
% 2.98/1.44  
% 2.98/1.44  Timing (in seconds)
% 2.98/1.44  ----------------------
% 2.98/1.44  Preprocessing        : 0.33
% 2.98/1.44  Parsing              : 0.17
% 2.98/1.44  CNF conversion       : 0.02
% 2.98/1.44  Main loop            : 0.29
% 2.98/1.44  Inferencing          : 0.12
% 2.98/1.44  Reduction            : 0.08
% 2.98/1.44  Demodulation         : 0.06
% 2.98/1.44  BG Simplification    : 0.02
% 2.98/1.44  Subsumption          : 0.05
% 2.98/1.44  Abstraction          : 0.02
% 2.98/1.44  MUC search           : 0.00
% 2.98/1.44  Cooper               : 0.00
% 2.98/1.44  Total                : 0.66
% 2.98/1.44  Index Insertion      : 0.00
% 2.98/1.45  Index Deletion       : 0.00
% 2.98/1.45  Index Matching       : 0.00
% 2.98/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
