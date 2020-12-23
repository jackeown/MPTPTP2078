%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:43 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 996 expanded)
%              Number of leaves         :   32 ( 340 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 (2249 expanded)
%              Number of equality atoms :   44 ( 341 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_104,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_318,plain,(
    ! [C_95,B_96,A_97] :
      ( v1_xboole_0(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(B_96,A_97)))
      | ~ v1_xboole_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_337,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_318])).

tff(c_342,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_64,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56])).

tff(c_58,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_486,plain,(
    ! [B_119,C_120,A_121] :
      ( k1_xboole_0 = B_119
      | v1_funct_2(C_120,A_121,B_119)
      | k1_relset_1(A_121,B_119,C_120) != A_121
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_493,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_60,c_486])).

tff(c_507,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_493])).

tff(c_508,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_507])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_538,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_12])).

tff(c_540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_538])).

tff(c_542,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_146,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_2'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [A_54,B_55] :
      ( ~ v1_xboole_0(A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_157,plain,(
    ! [A_56,B_57] :
      ( ~ v1_xboole_0(A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_161,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_157,c_14])).

tff(c_171,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ v1_xboole_0(B_60)
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_156,c_161])).

tff(c_174,plain,(
    ! [A_61] :
      ( k1_xboole_0 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_12,c_171])).

tff(c_555,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_542,c_174])).

tff(c_541,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_548,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_541,c_174])).

tff(c_579,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_548])).

tff(c_26,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_44,plain,(
    ! [A_33] :
      ( v1_funct_2(k1_xboole_0,A_33,k1_xboole_0)
      | k1_xboole_0 = A_33
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_33,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_66,plain,(
    ! [A_33] :
      ( v1_funct_2(k1_xboole_0,A_33,k1_xboole_0)
      | k1_xboole_0 = A_33 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_44])).

tff(c_568,plain,(
    ! [A_33] :
      ( v1_funct_2('#skF_5',A_33,'#skF_5')
      | A_33 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_548,c_548,c_66])).

tff(c_802,plain,(
    ! [A_139] :
      ( v1_funct_2('#skF_4',A_139,'#skF_4')
      | A_139 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_579,c_579,c_568])).

tff(c_597,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_64])).

tff(c_815,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_802,c_597])).

tff(c_584,plain,(
    ! [A_122,B_123,C_124] :
      ( k1_relset_1(A_122,B_123,C_124) = k1_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_587,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_584])).

tff(c_589,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_587])).

tff(c_608,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_589])).

tff(c_571,plain,(
    ! [A_14] : m1_subset_1('#skF_5',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_26])).

tff(c_704,plain,(
    ! [A_131] : m1_subset_1('#skF_4',k1_zfmisc_1(A_131)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_571])).

tff(c_42,plain,(
    ! [A_30,B_31,C_32] :
      ( k1_relset_1(A_30,B_31,C_32) = k1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_708,plain,(
    ! [A_30,B_31] : k1_relset_1(A_30,B_31,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_704,c_42])).

tff(c_728,plain,(
    ! [A_30,B_31] : k1_relset_1(A_30,B_31,'#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_708])).

tff(c_820,plain,(
    ! [A_30,B_31] : k1_relset_1(A_30,B_31,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_728])).

tff(c_703,plain,(
    ! [A_14] : m1_subset_1('#skF_4',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_571])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    ! [C_35,B_34] :
      ( v1_funct_2(C_35,k1_xboole_0,B_34)
      | k1_relset_1(k1_xboole_0,B_34,C_35) != k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_68,plain,(
    ! [C_35,B_34] :
      ( v1_funct_2(C_35,k1_xboole_0,B_34)
      | k1_relset_1(k1_xboole_0,B_34,C_35) != k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_48])).

tff(c_859,plain,(
    ! [C_141,B_142] :
      ( v1_funct_2(C_141,'#skF_4',B_142)
      | k1_relset_1('#skF_4',B_142,C_141) != '#skF_4'
      | ~ m1_subset_1(C_141,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_555,c_555,c_555,c_68])).

tff(c_863,plain,(
    ! [B_142] :
      ( v1_funct_2('#skF_4','#skF_4',B_142)
      | k1_relset_1('#skF_4',B_142,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_703,c_859])).

tff(c_1184,plain,(
    ! [B_142] : v1_funct_2('#skF_4','#skF_4',B_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_863])).

tff(c_821,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_597])).

tff(c_1187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:17:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.57  
% 3.20/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.57  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.20/1.57  
% 3.20/1.57  %Foreground sorts:
% 3.20/1.57  
% 3.20/1.57  
% 3.20/1.57  %Background operators:
% 3.20/1.57  
% 3.20/1.57  
% 3.20/1.57  %Foreground operators:
% 3.20/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.20/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.20/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.20/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.20/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.20/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.20/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.20/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.57  
% 3.20/1.58  tff(f_117, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 3.20/1.58  tff(f_82, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.20/1.58  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.20/1.58  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.20/1.58  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.20/1.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.20/1.58  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.20/1.58  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.20/1.58  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.20/1.58  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.20/1.58  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.20/1.58  tff(c_318, plain, (![C_95, B_96, A_97]: (v1_xboole_0(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(B_96, A_97))) | ~v1_xboole_0(A_97))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.20/1.58  tff(c_337, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_318])).
% 3.20/1.58  tff(c_342, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_337])).
% 3.20/1.58  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.20/1.58  tff(c_56, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.20/1.58  tff(c_64, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56])).
% 3.20/1.58  tff(c_58, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.20/1.58  tff(c_486, plain, (![B_119, C_120, A_121]: (k1_xboole_0=B_119 | v1_funct_2(C_120, A_121, B_119) | k1_relset_1(A_121, B_119, C_120)!=A_121 | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_119))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.20/1.58  tff(c_493, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_60, c_486])).
% 3.20/1.58  tff(c_507, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_493])).
% 3.20/1.58  tff(c_508, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_64, c_507])).
% 3.20/1.58  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.58  tff(c_538, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_508, c_12])).
% 3.20/1.58  tff(c_540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_538])).
% 3.20/1.58  tff(c_542, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_337])).
% 3.20/1.58  tff(c_146, plain, (![A_54, B_55]: (r2_hidden('#skF_2'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.20/1.58  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.58  tff(c_156, plain, (![A_54, B_55]: (~v1_xboole_0(A_54) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_146, c_2])).
% 3.20/1.58  tff(c_157, plain, (![A_56, B_57]: (~v1_xboole_0(A_56) | r1_tarski(A_56, B_57))), inference(resolution, [status(thm)], [c_146, c_2])).
% 3.20/1.58  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.58  tff(c_161, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_157, c_14])).
% 3.20/1.58  tff(c_171, plain, (![B_60, A_61]: (B_60=A_61 | ~v1_xboole_0(B_60) | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_156, c_161])).
% 3.20/1.58  tff(c_174, plain, (![A_61]: (k1_xboole_0=A_61 | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_12, c_171])).
% 3.20/1.58  tff(c_555, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_542, c_174])).
% 3.20/1.58  tff(c_541, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_337])).
% 3.20/1.58  tff(c_548, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_541, c_174])).
% 3.20/1.58  tff(c_579, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_555, c_548])).
% 3.20/1.58  tff(c_26, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.20/1.58  tff(c_44, plain, (![A_33]: (v1_funct_2(k1_xboole_0, A_33, k1_xboole_0) | k1_xboole_0=A_33 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_33, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.20/1.58  tff(c_66, plain, (![A_33]: (v1_funct_2(k1_xboole_0, A_33, k1_xboole_0) | k1_xboole_0=A_33)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_44])).
% 3.20/1.58  tff(c_568, plain, (![A_33]: (v1_funct_2('#skF_5', A_33, '#skF_5') | A_33='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_548, c_548, c_548, c_66])).
% 3.20/1.58  tff(c_802, plain, (![A_139]: (v1_funct_2('#skF_4', A_139, '#skF_4') | A_139='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_579, c_579, c_579, c_568])).
% 3.20/1.58  tff(c_597, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_579, c_64])).
% 3.20/1.58  tff(c_815, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_802, c_597])).
% 3.20/1.58  tff(c_584, plain, (![A_122, B_123, C_124]: (k1_relset_1(A_122, B_123, C_124)=k1_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.20/1.58  tff(c_587, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_584])).
% 3.20/1.58  tff(c_589, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_587])).
% 3.20/1.58  tff(c_608, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_579, c_589])).
% 3.20/1.58  tff(c_571, plain, (![A_14]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_548, c_26])).
% 3.20/1.58  tff(c_704, plain, (![A_131]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_131)))), inference(demodulation, [status(thm), theory('equality')], [c_579, c_571])).
% 3.20/1.58  tff(c_42, plain, (![A_30, B_31, C_32]: (k1_relset_1(A_30, B_31, C_32)=k1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.20/1.58  tff(c_708, plain, (![A_30, B_31]: (k1_relset_1(A_30, B_31, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_704, c_42])).
% 3.20/1.58  tff(c_728, plain, (![A_30, B_31]: (k1_relset_1(A_30, B_31, '#skF_4')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_608, c_708])).
% 3.20/1.58  tff(c_820, plain, (![A_30, B_31]: (k1_relset_1(A_30, B_31, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_815, c_728])).
% 3.20/1.58  tff(c_703, plain, (![A_14]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_579, c_571])).
% 3.20/1.58  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.20/1.58  tff(c_48, plain, (![C_35, B_34]: (v1_funct_2(C_35, k1_xboole_0, B_34) | k1_relset_1(k1_xboole_0, B_34, C_35)!=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_34))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.20/1.58  tff(c_68, plain, (![C_35, B_34]: (v1_funct_2(C_35, k1_xboole_0, B_34) | k1_relset_1(k1_xboole_0, B_34, C_35)!=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_48])).
% 3.20/1.58  tff(c_859, plain, (![C_141, B_142]: (v1_funct_2(C_141, '#skF_4', B_142) | k1_relset_1('#skF_4', B_142, C_141)!='#skF_4' | ~m1_subset_1(C_141, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_555, c_555, c_555, c_555, c_68])).
% 3.20/1.58  tff(c_863, plain, (![B_142]: (v1_funct_2('#skF_4', '#skF_4', B_142) | k1_relset_1('#skF_4', B_142, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_703, c_859])).
% 3.20/1.58  tff(c_1184, plain, (![B_142]: (v1_funct_2('#skF_4', '#skF_4', B_142))), inference(demodulation, [status(thm), theory('equality')], [c_820, c_863])).
% 3.20/1.58  tff(c_821, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_815, c_597])).
% 3.20/1.58  tff(c_1187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1184, c_821])).
% 3.20/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.58  
% 3.20/1.58  Inference rules
% 3.20/1.58  ----------------------
% 3.20/1.58  #Ref     : 0
% 3.20/1.58  #Sup     : 220
% 3.20/1.58  #Fact    : 0
% 3.20/1.58  #Define  : 0
% 3.20/1.58  #Split   : 3
% 3.20/1.58  #Chain   : 0
% 3.20/1.58  #Close   : 0
% 3.20/1.58  
% 3.20/1.58  Ordering : KBO
% 3.20/1.58  
% 3.20/1.58  Simplification rules
% 3.20/1.58  ----------------------
% 3.20/1.58  #Subsume      : 31
% 3.20/1.58  #Demod        : 247
% 3.20/1.58  #Tautology    : 122
% 3.20/1.58  #SimpNegUnit  : 2
% 3.20/1.58  #BackRed      : 58
% 3.20/1.58  
% 3.20/1.58  #Partial instantiations: 0
% 3.20/1.58  #Strategies tried      : 1
% 3.20/1.58  
% 3.20/1.58  Timing (in seconds)
% 3.20/1.58  ----------------------
% 3.20/1.59  Preprocessing        : 0.35
% 3.20/1.59  Parsing              : 0.19
% 3.20/1.59  CNF conversion       : 0.03
% 3.20/1.59  Main loop            : 0.40
% 3.20/1.59  Inferencing          : 0.14
% 3.20/1.59  Reduction            : 0.12
% 3.20/1.59  Demodulation         : 0.09
% 3.20/1.59  BG Simplification    : 0.02
% 3.20/1.59  Subsumption          : 0.08
% 3.20/1.59  Abstraction          : 0.02
% 3.20/1.59  MUC search           : 0.00
% 3.20/1.59  Cooper               : 0.00
% 3.20/1.59  Total                : 0.79
% 3.20/1.59  Index Insertion      : 0.00
% 3.20/1.59  Index Deletion       : 0.00
% 3.20/1.59  Index Matching       : 0.00
% 3.20/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
