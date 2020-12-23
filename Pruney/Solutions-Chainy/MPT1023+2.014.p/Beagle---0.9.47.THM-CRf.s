%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:18 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 281 expanded)
%              Number of leaves         :   31 ( 109 expanded)
%              Depth                    :   12
%              Number of atoms          :  164 ( 855 expanded)
%              Number of equality atoms :   56 ( 208 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_56,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_70,plain,(
    ! [C_42,B_43,A_44] :
      ( v1_xboole_0(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(B_43,A_44)))
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_77,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_70])).

tff(c_79,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_80,plain,(
    ! [A_45,B_46,D_47] :
      ( r2_relset_1(A_45,B_46,D_47,D_47)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_85,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_80])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_61,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_69,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_61])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_87,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_95,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_87])).

tff(c_108,plain,(
    ! [B_58,A_59,C_60] :
      ( k1_xboole_0 = B_58
      | k1_relset_1(A_59,B_58,C_60) = A_59
      | ~ v1_funct_2(C_60,A_59,B_58)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_114,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_108])).

tff(c_120,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_95,c_114])).

tff(c_127,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_68,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_61])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_94,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_87])).

tff(c_111,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_108])).

tff(c_117,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_94,c_111])).

tff(c_121,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_166,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_1'(A_68,B_69),k1_relat_1(A_68))
      | B_69 = A_68
      | k1_relat_1(B_69) != k1_relat_1(A_68)
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_175,plain,(
    ! [B_69] :
      ( r2_hidden('#skF_1'('#skF_4',B_69),'#skF_2')
      | B_69 = '#skF_4'
      | k1_relat_1(B_69) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_166])).

tff(c_186,plain,(
    ! [B_71] :
      ( r2_hidden('#skF_1'('#skF_4',B_71),'#skF_2')
      | B_71 = '#skF_4'
      | k1_relat_1(B_71) != '#skF_2'
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_48,c_121,c_175])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_196,plain,(
    ! [B_73] :
      ( m1_subset_1('#skF_1'('#skF_4',B_73),'#skF_2')
      | B_73 = '#skF_4'
      | k1_relat_1(B_73) != '#skF_2'
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_186,c_6])).

tff(c_36,plain,(
    ! [E_32] :
      ( k1_funct_1('#skF_5',E_32) = k1_funct_1('#skF_4',E_32)
      | ~ m1_subset_1(E_32,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_200,plain,(
    ! [B_73] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_73)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_73))
      | B_73 = '#skF_4'
      | k1_relat_1(B_73) != '#skF_2'
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_196,c_36])).

tff(c_224,plain,(
    ! [B_76,A_77] :
      ( k1_funct_1(B_76,'#skF_1'(A_77,B_76)) != k1_funct_1(A_77,'#skF_1'(A_77,B_76))
      | B_76 = A_77
      | k1_relat_1(B_76) != k1_relat_1(A_77)
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_228,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_224])).

tff(c_234,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_42,c_127,c_68,c_48,c_127,c_121,c_228])).

tff(c_34,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_247,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_34])).

tff(c_257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_247])).

tff(c_258,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_266,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_2])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_266])).

tff(c_269,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_277,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_2])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_277])).

tff(c_280,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_49,plain,(
    ! [B_33,A_34] :
      ( ~ v1_xboole_0(B_33)
      | B_33 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_52,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_306,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_280,c_52])).

tff(c_281,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_78,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_70])).

tff(c_282,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_282])).

tff(c_300,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_313,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_300,c_52])).

tff(c_355,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_313])).

tff(c_315,plain,(
    ! [A_78,B_79,D_80] :
      ( r2_relset_1(A_78,B_79,D_80,D_80)
      | ~ m1_subset_1(D_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_320,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_315])).

tff(c_374,plain,(
    r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_320])).

tff(c_299,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_328,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_299,c_52])).

tff(c_337,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_328])).

tff(c_343,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_34])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_355,c_343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:22:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.37  
% 2.64/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.37  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.64/1.37  
% 2.64/1.37  %Foreground sorts:
% 2.64/1.37  
% 2.64/1.37  
% 2.64/1.37  %Background operators:
% 2.64/1.37  
% 2.64/1.37  
% 2.64/1.37  %Foreground operators:
% 2.64/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.64/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.37  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.64/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.64/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.64/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.64/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.64/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.64/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.64/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.64/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.64/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.64/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.37  
% 2.64/1.39  tff(f_118, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 2.64/1.39  tff(f_67, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.64/1.39  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.64/1.39  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.64/1.39  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.64/1.39  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.64/1.39  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 2.64/1.39  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.64/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.64/1.39  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.64/1.39  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.64/1.39  tff(c_70, plain, (![C_42, B_43, A_44]: (v1_xboole_0(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(B_43, A_44))) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.64/1.39  tff(c_77, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_70])).
% 2.64/1.39  tff(c_79, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_77])).
% 2.64/1.39  tff(c_80, plain, (![A_45, B_46, D_47]: (r2_relset_1(A_45, B_46, D_47, D_47) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.64/1.39  tff(c_85, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_80])).
% 2.64/1.39  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.64/1.39  tff(c_61, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.64/1.39  tff(c_69, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_61])).
% 2.64/1.39  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.64/1.39  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.64/1.39  tff(c_87, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.64/1.39  tff(c_95, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_87])).
% 2.64/1.39  tff(c_108, plain, (![B_58, A_59, C_60]: (k1_xboole_0=B_58 | k1_relset_1(A_59, B_58, C_60)=A_59 | ~v1_funct_2(C_60, A_59, B_58) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.64/1.39  tff(c_114, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_108])).
% 2.64/1.39  tff(c_120, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_95, c_114])).
% 2.64/1.39  tff(c_127, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_120])).
% 2.64/1.39  tff(c_68, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_61])).
% 2.64/1.39  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.64/1.39  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.64/1.39  tff(c_94, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_87])).
% 2.64/1.39  tff(c_111, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_108])).
% 2.64/1.39  tff(c_117, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_94, c_111])).
% 2.64/1.39  tff(c_121, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_117])).
% 2.64/1.39  tff(c_166, plain, (![A_68, B_69]: (r2_hidden('#skF_1'(A_68, B_69), k1_relat_1(A_68)) | B_69=A_68 | k1_relat_1(B_69)!=k1_relat_1(A_68) | ~v1_funct_1(B_69) | ~v1_relat_1(B_69) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.64/1.39  tff(c_175, plain, (![B_69]: (r2_hidden('#skF_1'('#skF_4', B_69), '#skF_2') | B_69='#skF_4' | k1_relat_1(B_69)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_69) | ~v1_relat_1(B_69) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_166])).
% 2.64/1.39  tff(c_186, plain, (![B_71]: (r2_hidden('#skF_1'('#skF_4', B_71), '#skF_2') | B_71='#skF_4' | k1_relat_1(B_71)!='#skF_2' | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_48, c_121, c_175])).
% 2.64/1.39  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.64/1.39  tff(c_196, plain, (![B_73]: (m1_subset_1('#skF_1'('#skF_4', B_73), '#skF_2') | B_73='#skF_4' | k1_relat_1(B_73)!='#skF_2' | ~v1_funct_1(B_73) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_186, c_6])).
% 2.64/1.39  tff(c_36, plain, (![E_32]: (k1_funct_1('#skF_5', E_32)=k1_funct_1('#skF_4', E_32) | ~m1_subset_1(E_32, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.64/1.39  tff(c_200, plain, (![B_73]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_73))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_73)) | B_73='#skF_4' | k1_relat_1(B_73)!='#skF_2' | ~v1_funct_1(B_73) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_196, c_36])).
% 2.64/1.39  tff(c_224, plain, (![B_76, A_77]: (k1_funct_1(B_76, '#skF_1'(A_77, B_76))!=k1_funct_1(A_77, '#skF_1'(A_77, B_76)) | B_76=A_77 | k1_relat_1(B_76)!=k1_relat_1(A_77) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.64/1.39  tff(c_228, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_200, c_224])).
% 2.64/1.39  tff(c_234, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_42, c_127, c_68, c_48, c_127, c_121, c_228])).
% 2.64/1.39  tff(c_34, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.64/1.39  tff(c_247, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_34])).
% 2.64/1.39  tff(c_257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_247])).
% 2.64/1.39  tff(c_258, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_120])).
% 2.64/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.64/1.39  tff(c_266, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_258, c_2])).
% 2.64/1.39  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_266])).
% 2.64/1.39  tff(c_269, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_117])).
% 2.64/1.39  tff(c_277, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_2])).
% 2.64/1.39  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_277])).
% 2.64/1.39  tff(c_280, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_77])).
% 2.64/1.39  tff(c_49, plain, (![B_33, A_34]: (~v1_xboole_0(B_33) | B_33=A_34 | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.64/1.39  tff(c_52, plain, (![A_34]: (k1_xboole_0=A_34 | ~v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_2, c_49])).
% 2.64/1.39  tff(c_306, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_280, c_52])).
% 2.64/1.39  tff(c_281, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_77])).
% 2.64/1.39  tff(c_78, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_70])).
% 2.64/1.39  tff(c_282, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_78])).
% 2.64/1.39  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_282])).
% 2.64/1.39  tff(c_300, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_78])).
% 2.64/1.39  tff(c_313, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_300, c_52])).
% 2.64/1.39  tff(c_355, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_306, c_313])).
% 2.64/1.39  tff(c_315, plain, (![A_78, B_79, D_80]: (r2_relset_1(A_78, B_79, D_80, D_80) | ~m1_subset_1(D_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.64/1.39  tff(c_320, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_315])).
% 2.64/1.39  tff(c_374, plain, (r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_355, c_320])).
% 2.64/1.39  tff(c_299, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_78])).
% 2.64/1.39  tff(c_328, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_299, c_52])).
% 2.64/1.39  tff(c_337, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_306, c_328])).
% 2.64/1.39  tff(c_343, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_34])).
% 2.64/1.39  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_374, c_355, c_343])).
% 2.64/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.39  
% 2.64/1.39  Inference rules
% 2.64/1.39  ----------------------
% 2.64/1.39  #Ref     : 1
% 2.64/1.39  #Sup     : 60
% 2.64/1.39  #Fact    : 0
% 2.64/1.39  #Define  : 0
% 2.64/1.39  #Split   : 4
% 2.64/1.39  #Chain   : 0
% 2.64/1.39  #Close   : 0
% 2.64/1.39  
% 2.64/1.39  Ordering : KBO
% 2.64/1.39  
% 2.64/1.39  Simplification rules
% 2.64/1.39  ----------------------
% 2.64/1.39  #Subsume      : 6
% 2.64/1.39  #Demod        : 125
% 2.64/1.39  #Tautology    : 46
% 2.64/1.39  #SimpNegUnit  : 2
% 2.64/1.39  #BackRed      : 38
% 2.64/1.39  
% 2.64/1.39  #Partial instantiations: 0
% 2.64/1.39  #Strategies tried      : 1
% 2.64/1.39  
% 2.64/1.39  Timing (in seconds)
% 2.64/1.39  ----------------------
% 2.64/1.39  Preprocessing        : 0.34
% 2.64/1.39  Parsing              : 0.17
% 2.64/1.39  CNF conversion       : 0.02
% 2.64/1.40  Main loop            : 0.27
% 2.64/1.40  Inferencing          : 0.09
% 2.64/1.40  Reduction            : 0.08
% 2.64/1.40  Demodulation         : 0.06
% 2.64/1.40  BG Simplification    : 0.02
% 2.64/1.40  Subsumption          : 0.05
% 2.64/1.40  Abstraction          : 0.01
% 2.64/1.40  MUC search           : 0.00
% 2.64/1.40  Cooper               : 0.00
% 2.64/1.40  Total                : 0.65
% 2.64/1.40  Index Insertion      : 0.00
% 2.64/1.40  Index Deletion       : 0.00
% 2.64/1.40  Index Matching       : 0.00
% 2.64/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
