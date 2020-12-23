%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:55 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 404 expanded)
%              Number of leaves         :   29 ( 141 expanded)
%              Depth                    :   11
%              Number of atoms          :  165 (1290 expanded)
%              Number of equality atoms :   30 ( 384 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_131,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( r2_relset_1(A_40,B_41,C_42,C_42)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_154,plain,(
    ! [C_44] :
      ( r2_relset_1('#skF_3','#skF_4',C_44,C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_131])).

tff(c_160,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_154])).

tff(c_44,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_44])).

tff(c_28,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_43,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_50,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_43])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_111,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_partfun1(C_37,A_38)
      | ~ v1_funct_2(C_37,A_38,B_39)
      | ~ v1_funct_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | v1_xboole_0(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_114,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_111])).

tff(c_126,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_114])).

tff(c_144,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_49,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6])).

tff(c_147,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_144,c_49])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_147])).

tff(c_152,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_153,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_36,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_34,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_117,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_111])).

tff(c_129,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_117])).

tff(c_161,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_129])).

tff(c_30,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_162,plain,(
    ! [D_45,C_46,A_47,B_48] :
      ( D_45 = C_46
      | ~ r1_partfun1(C_46,D_45)
      | ~ v1_partfun1(D_45,A_47)
      | ~ v1_partfun1(C_46,A_47)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_1(D_45)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_164,plain,(
    ! [A_47,B_48] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_47)
      | ~ v1_partfun1('#skF_5',A_47)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_162])).

tff(c_167,plain,(
    ! [A_47,B_48] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_47)
      | ~ v1_partfun1('#skF_5',A_47)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_164])).

tff(c_171,plain,(
    ! [A_50,B_51] :
      ( ~ v1_partfun1('#skF_6',A_50)
      | ~ v1_partfun1('#skF_5',A_50)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_174,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_38,c_171])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_152,c_161,c_174])).

tff(c_185,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_26,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_189,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_26])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_189])).

tff(c_200,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_226,plain,(
    ! [A_53] :
      ( A_53 = '#skF_4'
      | ~ v1_xboole_0(A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_6])).

tff(c_230,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_226])).

tff(c_231,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_8])).

tff(c_12,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_215,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_12])).

tff(c_199,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_205,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_199])).

tff(c_264,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_205,c_32])).

tff(c_277,plain,(
    ! [C_60,B_61,A_62] :
      ( ~ v1_xboole_0(C_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(C_60))
      | ~ r2_hidden(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_279,plain,(
    ! [A_62] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_62,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_264,c_277])).

tff(c_288,plain,(
    ! [A_63] : ~ r2_hidden(A_63,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_279])).

tff(c_293,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_288])).

tff(c_225,plain,(
    ! [A_5] :
      ( A_5 = '#skF_4'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_6])).

tff(c_297,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_293,c_225])).

tff(c_300,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_264])).

tff(c_316,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( r2_relset_1(A_65,B_66,C_67,C_67)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_320,plain,(
    ! [A_6,C_67,D_68] :
      ( r2_relset_1(A_6,'#skF_4',C_67,C_67)
      | ~ m1_subset_1(D_68,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_6,'#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_316])).

tff(c_322,plain,(
    ! [A_6,C_67,D_68] :
      ( r2_relset_1(A_6,'#skF_4',C_67,C_67)
      | ~ m1_subset_1(D_68,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_67,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_320])).

tff(c_362,plain,(
    ! [D_68] : ~ m1_subset_1(D_68,k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_362,c_300])).

tff(c_373,plain,(
    ! [A_77,C_78] :
      ( r2_relset_1(A_77,'#skF_4',C_78,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_376,plain,(
    ! [A_77] : r2_relset_1(A_77,'#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_300,c_373])).

tff(c_263,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_205,c_38])).

tff(c_281,plain,(
    ! [A_62] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_62,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_263,c_277])).

tff(c_310,plain,(
    ! [A_64] : ~ r2_hidden(A_64,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_281])).

tff(c_315,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_310])).

tff(c_326,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_315,c_225])).

tff(c_224,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_26])).

tff(c_301,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_224])).

tff(c_361,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_301])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.28  
% 2.06/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.28  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.06/1.28  
% 2.06/1.28  %Foreground sorts:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Background operators:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Foreground operators:
% 2.06/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.28  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.06/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.06/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.06/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.06/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.28  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.06/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.28  
% 2.37/1.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.37/1.30  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.37/1.30  tff(f_110, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 2.37/1.30  tff(f_56, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.37/1.30  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.37/1.30  tff(f_70, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.37/1.30  tff(f_87, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.37/1.30  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.37/1.30  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.37/1.30  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.30  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.37/1.30  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.37/1.30  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.37/1.30  tff(c_131, plain, (![A_40, B_41, C_42, D_43]: (r2_relset_1(A_40, B_41, C_42, C_42) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.37/1.30  tff(c_154, plain, (![C_44]: (r2_relset_1('#skF_3', '#skF_4', C_44, C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_38, c_131])).
% 2.37/1.30  tff(c_160, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_32, c_154])).
% 2.37/1.30  tff(c_44, plain, (![A_25]: (k1_xboole_0=A_25 | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.37/1.30  tff(c_48, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_44])).
% 2.37/1.30  tff(c_28, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.37/1.30  tff(c_43, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_28])).
% 2.37/1.30  tff(c_50, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_43])).
% 2.37/1.30  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.37/1.30  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.37/1.30  tff(c_111, plain, (![C_37, A_38, B_39]: (v1_partfun1(C_37, A_38) | ~v1_funct_2(C_37, A_38, B_39) | ~v1_funct_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | v1_xboole_0(B_39))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.37/1.30  tff(c_114, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_111])).
% 2.37/1.30  tff(c_126, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_114])).
% 2.37/1.30  tff(c_144, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_126])).
% 2.37/1.30  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.37/1.30  tff(c_49, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6])).
% 2.37/1.30  tff(c_147, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_144, c_49])).
% 2.37/1.30  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_147])).
% 2.37/1.30  tff(c_152, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_126])).
% 2.37/1.30  tff(c_153, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_126])).
% 2.37/1.30  tff(c_36, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.37/1.30  tff(c_34, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.37/1.30  tff(c_117, plain, (v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_32, c_111])).
% 2.37/1.30  tff(c_129, plain, (v1_partfun1('#skF_6', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_117])).
% 2.37/1.30  tff(c_161, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_153, c_129])).
% 2.37/1.30  tff(c_30, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.37/1.30  tff(c_162, plain, (![D_45, C_46, A_47, B_48]: (D_45=C_46 | ~r1_partfun1(C_46, D_45) | ~v1_partfun1(D_45, A_47) | ~v1_partfun1(C_46, A_47) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_1(D_45) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_1(C_46))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.37/1.30  tff(c_164, plain, (![A_47, B_48]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_47) | ~v1_partfun1('#skF_5', A_47) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_162])).
% 2.37/1.30  tff(c_167, plain, (![A_47, B_48]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_47) | ~v1_partfun1('#skF_5', A_47) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_164])).
% 2.37/1.30  tff(c_171, plain, (![A_50, B_51]: (~v1_partfun1('#skF_6', A_50) | ~v1_partfun1('#skF_5', A_50) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(splitLeft, [status(thm)], [c_167])).
% 2.37/1.30  tff(c_174, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_38, c_171])).
% 2.37/1.30  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_152, c_161, c_174])).
% 2.37/1.30  tff(c_185, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_167])).
% 2.37/1.30  tff(c_26, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.37/1.30  tff(c_189, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_26])).
% 2.37/1.30  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_189])).
% 2.37/1.30  tff(c_200, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 2.37/1.30  tff(c_226, plain, (![A_53]: (A_53='#skF_4' | ~v1_xboole_0(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_6])).
% 2.37/1.30  tff(c_230, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_8, c_226])).
% 2.37/1.30  tff(c_231, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_8])).
% 2.37/1.30  tff(c_12, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.37/1.30  tff(c_215, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_12])).
% 2.37/1.30  tff(c_199, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 2.37/1.30  tff(c_205, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_199])).
% 2.37/1.30  tff(c_264, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_205, c_32])).
% 2.37/1.30  tff(c_277, plain, (![C_60, B_61, A_62]: (~v1_xboole_0(C_60) | ~m1_subset_1(B_61, k1_zfmisc_1(C_60)) | ~r2_hidden(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.37/1.30  tff(c_279, plain, (![A_62]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_62, '#skF_6'))), inference(resolution, [status(thm)], [c_264, c_277])).
% 2.37/1.30  tff(c_288, plain, (![A_63]: (~r2_hidden(A_63, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_279])).
% 2.37/1.30  tff(c_293, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_288])).
% 2.37/1.30  tff(c_225, plain, (![A_5]: (A_5='#skF_4' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_6])).
% 2.37/1.30  tff(c_297, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_293, c_225])).
% 2.37/1.30  tff(c_300, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_264])).
% 2.37/1.30  tff(c_316, plain, (![A_65, B_66, C_67, D_68]: (r2_relset_1(A_65, B_66, C_67, C_67) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.37/1.30  tff(c_320, plain, (![A_6, C_67, D_68]: (r2_relset_1(A_6, '#skF_4', C_67, C_67) | ~m1_subset_1(D_68, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_6, '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_215, c_316])).
% 2.37/1.30  tff(c_322, plain, (![A_6, C_67, D_68]: (r2_relset_1(A_6, '#skF_4', C_67, C_67) | ~m1_subset_1(D_68, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_67, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_320])).
% 2.37/1.30  tff(c_362, plain, (![D_68]: (~m1_subset_1(D_68, k1_zfmisc_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_322])).
% 2.37/1.30  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_362, c_300])).
% 2.37/1.30  tff(c_373, plain, (![A_77, C_78]: (r2_relset_1(A_77, '#skF_4', C_78, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_322])).
% 2.37/1.30  tff(c_376, plain, (![A_77]: (r2_relset_1(A_77, '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_300, c_373])).
% 2.37/1.30  tff(c_263, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_205, c_38])).
% 2.37/1.30  tff(c_281, plain, (![A_62]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_62, '#skF_5'))), inference(resolution, [status(thm)], [c_263, c_277])).
% 2.37/1.30  tff(c_310, plain, (![A_64]: (~r2_hidden(A_64, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_281])).
% 2.37/1.30  tff(c_315, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_310])).
% 2.37/1.30  tff(c_326, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_315, c_225])).
% 2.37/1.30  tff(c_224, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_26])).
% 2.37/1.30  tff(c_301, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_297, c_224])).
% 2.37/1.30  tff(c_361, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_326, c_301])).
% 2.37/1.30  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_376, c_361])).
% 2.37/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.30  
% 2.37/1.30  Inference rules
% 2.37/1.30  ----------------------
% 2.37/1.30  #Ref     : 0
% 2.37/1.30  #Sup     : 67
% 2.37/1.30  #Fact    : 0
% 2.37/1.30  #Define  : 0
% 2.37/1.30  #Split   : 6
% 2.37/1.30  #Chain   : 0
% 2.37/1.30  #Close   : 0
% 2.37/1.30  
% 2.37/1.30  Ordering : KBO
% 2.37/1.30  
% 2.37/1.30  Simplification rules
% 2.37/1.30  ----------------------
% 2.37/1.30  #Subsume      : 6
% 2.37/1.30  #Demod        : 78
% 2.37/1.30  #Tautology    : 47
% 2.37/1.30  #SimpNegUnit  : 3
% 2.37/1.30  #BackRed      : 26
% 2.37/1.30  
% 2.37/1.30  #Partial instantiations: 0
% 2.37/1.30  #Strategies tried      : 1
% 2.37/1.30  
% 2.37/1.30  Timing (in seconds)
% 2.37/1.30  ----------------------
% 2.37/1.30  Preprocessing        : 0.30
% 2.37/1.30  Parsing              : 0.17
% 2.37/1.30  CNF conversion       : 0.02
% 2.37/1.30  Main loop            : 0.22
% 2.37/1.30  Inferencing          : 0.08
% 2.37/1.30  Reduction            : 0.07
% 2.37/1.30  Demodulation         : 0.05
% 2.37/1.30  BG Simplification    : 0.01
% 2.37/1.30  Subsumption          : 0.03
% 2.37/1.30  Abstraction          : 0.01
% 2.37/1.30  MUC search           : 0.00
% 2.37/1.30  Cooper               : 0.00
% 2.37/1.30  Total                : 0.57
% 2.37/1.30  Index Insertion      : 0.00
% 2.37/1.30  Index Deletion       : 0.00
% 2.37/1.30  Index Matching       : 0.00
% 2.37/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
