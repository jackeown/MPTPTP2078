%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:19 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 403 expanded)
%              Number of leaves         :   33 ( 151 expanded)
%              Depth                    :   15
%              Number of atoms          :  167 (1120 expanded)
%              Number of equality atoms :   34 ( 199 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_130,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_98,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_79,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_88,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_105,plain,(
    ! [C_50,A_51,B_52] :
      ( v4_relat_1(C_50,A_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_114,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_105])).

tff(c_119,plain,(
    ! [B_57,A_58] :
      ( k1_relat_1(B_57) = A_58
      | ~ v1_partfun1(B_57,A_58)
      | ~ v4_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_122,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_119])).

tff(c_125,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_122])).

tff(c_126,plain,(
    ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_44,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_128,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_partfun1(C_61,A_62)
      | ~ v1_funct_2(C_61,A_62,B_63)
      | ~ v1_funct_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | v1_xboole_0(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_135,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_128])).

tff(c_139,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_135])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_126,c_139])).

tff(c_142,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_34,plain,(
    ! [A_24] : k6_relat_1(A_24) = k6_partfun1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_4),B_4),k1_relat_1(B_4))
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_155,plain,(
    ! [B_66] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_66),B_66),k1_relat_1(B_66))
      | k6_partfun1(k1_relat_1(B_66)) = B_66
      | ~ v1_funct_1(B_66)
      | ~ v1_relat_1(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12])).

tff(c_161,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_155])).

tff(c_167,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_46,c_142,c_142,c_161])).

tff(c_183,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_38,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_184,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_38])).

tff(c_248,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( r2_funct_2(A_78,B_79,C_80,C_80)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_2(D_81,A_78,B_79)
      | ~ v1_funct_1(D_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_2(C_80,A_78,B_79)
      | ~ v1_funct_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_253,plain,(
    ! [C_80] :
      ( r2_funct_2('#skF_2','#skF_2',C_80,C_80)
      | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_80,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_80) ) ),
    inference(resolution,[status(thm)],[c_42,c_248])).

tff(c_258,plain,(
    ! [C_82] :
      ( r2_funct_2('#skF_2','#skF_2',C_82,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_2(C_82,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_253])).

tff(c_263,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_258])).

tff(c_267,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_263])).

tff(c_269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_267])).

tff(c_271,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_10,plain,(
    ! [B_4] :
      ( k1_funct_1(B_4,'#skF_1'(k1_relat_1(B_4),B_4)) != '#skF_1'(k1_relat_1(B_4),B_4)
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_292,plain,(
    ! [B_83] :
      ( k1_funct_1(B_83,'#skF_1'(k1_relat_1(B_83),B_83)) != '#skF_1'(k1_relat_1(B_83),B_83)
      | k6_partfun1(k1_relat_1(B_83)) = B_83
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10])).

tff(c_295,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_292])).

tff(c_297,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_46,c_142,c_142,c_295])).

tff(c_298,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_297])).

tff(c_270,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( m1_subset_1(B_2,A_1)
      | ~ r2_hidden(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_274,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_270,c_2])).

tff(c_277,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_274])).

tff(c_40,plain,(
    ! [C_33] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_33) = C_33
      | ~ m1_subset_1(C_33,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_284,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_277,c_40])).

tff(c_316,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k3_funct_2(A_85,B_86,C_87,D_88) = k1_funct_1(C_87,D_88)
      | ~ m1_subset_1(D_88,A_85)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_2(C_87,A_85,B_86)
      | ~ v1_funct_1(C_87)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_320,plain,(
    ! [B_86,C_87] :
      ( k3_funct_2('#skF_2',B_86,C_87,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_87,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_86)))
      | ~ v1_funct_2(C_87,'#skF_2',B_86)
      | ~ v1_funct_1(C_87)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_277,c_316])).

tff(c_333,plain,(
    ! [B_89,C_90] :
      ( k3_funct_2('#skF_2',B_89,C_90,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_90,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_89)))
      | ~ v1_funct_2(C_90,'#skF_2',B_89)
      | ~ v1_funct_1(C_90) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_320])).

tff(c_340,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_333])).

tff(c_344,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_284,c_340])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.30  
% 2.35/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.30  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.35/1.30  
% 2.35/1.30  %Foreground sorts:
% 2.35/1.30  
% 2.35/1.30  
% 2.35/1.30  %Background operators:
% 2.35/1.30  
% 2.35/1.30  
% 2.35/1.30  %Foreground operators:
% 2.35/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.35/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.35/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.30  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.35/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.35/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.35/1.30  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.35/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.35/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.35/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.35/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.35/1.30  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.35/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.35/1.30  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.35/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.30  
% 2.35/1.31  tff(f_130, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 2.35/1.31  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.35/1.31  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.35/1.31  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.35/1.31  tff(f_75, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.35/1.31  tff(f_98, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.35/1.31  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.35/1.31  tff(f_112, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 2.35/1.31  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.35/1.31  tff(f_96, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.35/1.31  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.35/1.31  tff(c_79, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.35/1.31  tff(c_88, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_79])).
% 2.35/1.31  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.35/1.31  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.35/1.31  tff(c_105, plain, (![C_50, A_51, B_52]: (v4_relat_1(C_50, A_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.35/1.31  tff(c_114, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_105])).
% 2.35/1.31  tff(c_119, plain, (![B_57, A_58]: (k1_relat_1(B_57)=A_58 | ~v1_partfun1(B_57, A_58) | ~v4_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.35/1.31  tff(c_122, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_119])).
% 2.35/1.31  tff(c_125, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_122])).
% 2.35/1.31  tff(c_126, plain, (~v1_partfun1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_125])).
% 2.35/1.31  tff(c_44, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.35/1.31  tff(c_128, plain, (![C_61, A_62, B_63]: (v1_partfun1(C_61, A_62) | ~v1_funct_2(C_61, A_62, B_63) | ~v1_funct_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | v1_xboole_0(B_63))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.35/1.31  tff(c_135, plain, (v1_partfun1('#skF_3', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_128])).
% 2.35/1.31  tff(c_139, plain, (v1_partfun1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_135])).
% 2.35/1.31  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_126, c_139])).
% 2.35/1.31  tff(c_142, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_125])).
% 2.35/1.31  tff(c_34, plain, (![A_24]: (k6_relat_1(A_24)=k6_partfun1(A_24))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.35/1.31  tff(c_12, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.35/1.31  tff(c_155, plain, (![B_66]: (r2_hidden('#skF_1'(k1_relat_1(B_66), B_66), k1_relat_1(B_66)) | k6_partfun1(k1_relat_1(B_66))=B_66 | ~v1_funct_1(B_66) | ~v1_relat_1(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12])).
% 2.35/1.31  tff(c_161, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_142, c_155])).
% 2.35/1.31  tff(c_167, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_46, c_142, c_142, c_161])).
% 2.35/1.31  tff(c_183, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_167])).
% 2.35/1.31  tff(c_38, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.35/1.31  tff(c_184, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_38])).
% 2.35/1.31  tff(c_248, plain, (![A_78, B_79, C_80, D_81]: (r2_funct_2(A_78, B_79, C_80, C_80) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_2(D_81, A_78, B_79) | ~v1_funct_1(D_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_2(C_80, A_78, B_79) | ~v1_funct_1(C_80))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.35/1.31  tff(c_253, plain, (![C_80]: (r2_funct_2('#skF_2', '#skF_2', C_80, C_80) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(C_80, '#skF_2', '#skF_2') | ~v1_funct_1(C_80))), inference(resolution, [status(thm)], [c_42, c_248])).
% 2.35/1.31  tff(c_258, plain, (![C_82]: (r2_funct_2('#skF_2', '#skF_2', C_82, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2(C_82, '#skF_2', '#skF_2') | ~v1_funct_1(C_82))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_253])).
% 2.35/1.31  tff(c_263, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_258])).
% 2.35/1.31  tff(c_267, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_263])).
% 2.35/1.31  tff(c_269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_184, c_267])).
% 2.35/1.31  tff(c_271, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_167])).
% 2.35/1.31  tff(c_10, plain, (![B_4]: (k1_funct_1(B_4, '#skF_1'(k1_relat_1(B_4), B_4))!='#skF_1'(k1_relat_1(B_4), B_4) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.35/1.31  tff(c_292, plain, (![B_83]: (k1_funct_1(B_83, '#skF_1'(k1_relat_1(B_83), B_83))!='#skF_1'(k1_relat_1(B_83), B_83) | k6_partfun1(k1_relat_1(B_83))=B_83 | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10])).
% 2.35/1.31  tff(c_295, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_142, c_292])).
% 2.35/1.31  tff(c_297, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_46, c_142, c_142, c_295])).
% 2.35/1.31  tff(c_298, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_271, c_297])).
% 2.35/1.31  tff(c_270, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_167])).
% 2.35/1.31  tff(c_2, plain, (![B_2, A_1]: (m1_subset_1(B_2, A_1) | ~r2_hidden(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.35/1.31  tff(c_274, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_270, c_2])).
% 2.35/1.31  tff(c_277, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_274])).
% 2.35/1.31  tff(c_40, plain, (![C_33]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_33)=C_33 | ~m1_subset_1(C_33, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.35/1.31  tff(c_284, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_277, c_40])).
% 2.35/1.31  tff(c_316, plain, (![A_85, B_86, C_87, D_88]: (k3_funct_2(A_85, B_86, C_87, D_88)=k1_funct_1(C_87, D_88) | ~m1_subset_1(D_88, A_85) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_2(C_87, A_85, B_86) | ~v1_funct_1(C_87) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.35/1.31  tff(c_320, plain, (![B_86, C_87]: (k3_funct_2('#skF_2', B_86, C_87, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_87, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_86))) | ~v1_funct_2(C_87, '#skF_2', B_86) | ~v1_funct_1(C_87) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_277, c_316])).
% 2.35/1.31  tff(c_333, plain, (![B_89, C_90]: (k3_funct_2('#skF_2', B_89, C_90, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_90, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_89))) | ~v1_funct_2(C_90, '#skF_2', B_89) | ~v1_funct_1(C_90))), inference(negUnitSimplification, [status(thm)], [c_48, c_320])).
% 2.35/1.31  tff(c_340, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_333])).
% 2.35/1.31  tff(c_344, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_284, c_340])).
% 2.35/1.31  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_298, c_344])).
% 2.35/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.31  
% 2.35/1.31  Inference rules
% 2.35/1.31  ----------------------
% 2.35/1.31  #Ref     : 0
% 2.35/1.31  #Sup     : 55
% 2.35/1.31  #Fact    : 0
% 2.35/1.31  #Define  : 0
% 2.35/1.31  #Split   : 4
% 2.35/1.31  #Chain   : 0
% 2.35/1.31  #Close   : 0
% 2.35/1.31  
% 2.35/1.31  Ordering : KBO
% 2.35/1.31  
% 2.35/1.31  Simplification rules
% 2.35/1.31  ----------------------
% 2.35/1.31  #Subsume      : 11
% 2.35/1.31  #Demod        : 78
% 2.35/1.31  #Tautology    : 25
% 2.35/1.32  #SimpNegUnit  : 15
% 2.35/1.32  #BackRed      : 1
% 2.35/1.32  
% 2.35/1.32  #Partial instantiations: 0
% 2.35/1.32  #Strategies tried      : 1
% 2.35/1.32  
% 2.35/1.32  Timing (in seconds)
% 2.35/1.32  ----------------------
% 2.35/1.32  Preprocessing        : 0.32
% 2.35/1.32  Parsing              : 0.17
% 2.35/1.32  CNF conversion       : 0.02
% 2.35/1.32  Main loop            : 0.23
% 2.35/1.32  Inferencing          : 0.08
% 2.35/1.32  Reduction            : 0.07
% 2.35/1.32  Demodulation         : 0.05
% 2.35/1.32  BG Simplification    : 0.02
% 2.35/1.32  Subsumption          : 0.04
% 2.35/1.32  Abstraction          : 0.01
% 2.35/1.32  MUC search           : 0.00
% 2.35/1.32  Cooper               : 0.00
% 2.35/1.32  Total                : 0.58
% 2.35/1.32  Index Insertion      : 0.00
% 2.35/1.32  Index Deletion       : 0.00
% 2.35/1.32  Index Matching       : 0.00
% 2.35/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
