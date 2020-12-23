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
% DateTime   : Thu Dec  3 10:13:43 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 163 expanded)
%              Number of leaves         :   32 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  111 ( 367 expanded)
%              Number of equality atoms :   33 (  90 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_900,plain,(
    ! [A_174,B_175,C_176,D_177] :
      ( r2_relset_1(A_174,B_175,C_176,C_176)
      | ~ m1_subset_1(D_177,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_911,plain,(
    ! [C_179] :
      ( r2_relset_1('#skF_1','#skF_2',C_179,C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_42,c_900])).

tff(c_914,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_911])).

tff(c_73,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_81,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_73])).

tff(c_40,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_676,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_686,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_676])).

tff(c_769,plain,(
    ! [B_156,A_157,C_158] :
      ( k1_xboole_0 = B_156
      | k1_relset_1(A_157,B_156,C_158) = A_157
      | ~ v1_funct_2(C_158,A_157,B_156)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_157,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_772,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_769])).

tff(c_781,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_686,c_772])).

tff(c_783,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_781])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( v4_relat_1(B_4,A_3)
      | ~ r1_tarski(k1_relat_1(B_4),A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_788,plain,(
    ! [A_3] :
      ( v4_relat_1('#skF_4',A_3)
      | ~ r1_tarski('#skF_1',A_3)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_8])).

tff(c_808,plain,(
    ! [A_160] :
      ( v4_relat_1('#skF_4',A_160)
      | ~ r1_tarski('#skF_1',A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_788])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( k7_relat_1(B_6,A_5) = B_6
      | ~ v4_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_814,plain,(
    ! [A_160] :
      ( k7_relat_1('#skF_4',A_160) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_160) ) ),
    inference(resolution,[status(thm)],[c_808,c_12])).

tff(c_819,plain,(
    ! [A_161] :
      ( k7_relat_1('#skF_4',A_161) = '#skF_4'
      | ~ r1_tarski('#skF_1',A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_814])).

tff(c_828,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_819])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_734,plain,(
    ! [A_146,B_147,C_148,D_149] :
      ( k2_partfun1(A_146,B_147,C_148,D_149) = k7_relat_1(C_148,D_149)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147)))
      | ~ v1_funct_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_736,plain,(
    ! [D_149] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_149) = k7_relat_1('#skF_4',D_149)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_734])).

tff(c_743,plain,(
    ! [D_149] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_149) = k7_relat_1('#skF_4',D_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_736])).

tff(c_38,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_744,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_38])).

tff(c_829,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_744])).

tff(c_853,plain,(
    ! [A_168,B_169,C_170,D_171] :
      ( r2_relset_1(A_168,B_169,C_170,C_170)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_863,plain,(
    ! [C_172] :
      ( r2_relset_1('#skF_1','#skF_2',C_172,C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_42,c_853])).

tff(c_865,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_863])).

tff(c_869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_829,c_865])).

tff(c_870,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_781])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_893,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_870,c_4])).

tff(c_916,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_42])).

tff(c_94,plain,(
    ! [C_35,A_36,B_37] :
      ( v4_relat_1(C_35,A_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_100,plain,(
    ! [C_35,A_1] :
      ( v4_relat_1(C_35,A_1)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_94])).

tff(c_1030,plain,(
    ! [C_191,A_192] :
      ( v4_relat_1(C_191,A_192)
      | ~ m1_subset_1(C_191,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_100])).

tff(c_1039,plain,(
    ! [A_193] : v4_relat_1('#skF_4',A_193) ),
    inference(resolution,[status(thm)],[c_916,c_1030])).

tff(c_1042,plain,(
    ! [A_193] :
      ( k7_relat_1('#skF_4',A_193) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1039,c_12])).

tff(c_1045,plain,(
    ! [A_193] : k7_relat_1('#skF_4',A_193) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1042])).

tff(c_1046,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1045,c_744])).

tff(c_1051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_1046])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:59:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.51  
% 3.44/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.51  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.44/1.51  
% 3.44/1.51  %Foreground sorts:
% 3.44/1.51  
% 3.44/1.51  
% 3.44/1.51  %Background operators:
% 3.44/1.51  
% 3.44/1.51  
% 3.44/1.51  %Foreground operators:
% 3.44/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.44/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.51  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.44/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.44/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.44/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.44/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.44/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.44/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.51  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.44/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.44/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.51  
% 3.58/1.53  tff(f_98, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 3.58/1.53  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.58/1.53  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.58/1.53  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.58/1.53  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.58/1.53  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.58/1.53  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.58/1.53  tff(f_87, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.58/1.53  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.58/1.53  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.58/1.53  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.58/1.53  tff(c_900, plain, (![A_174, B_175, C_176, D_177]: (r2_relset_1(A_174, B_175, C_176, C_176) | ~m1_subset_1(D_177, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.58/1.53  tff(c_911, plain, (![C_179]: (r2_relset_1('#skF_1', '#skF_2', C_179, C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_42, c_900])).
% 3.58/1.53  tff(c_914, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_911])).
% 3.58/1.53  tff(c_73, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.58/1.53  tff(c_81, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_73])).
% 3.58/1.53  tff(c_40, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.58/1.53  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.58/1.53  tff(c_676, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.58/1.53  tff(c_686, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_676])).
% 3.58/1.53  tff(c_769, plain, (![B_156, A_157, C_158]: (k1_xboole_0=B_156 | k1_relset_1(A_157, B_156, C_158)=A_157 | ~v1_funct_2(C_158, A_157, B_156) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.58/1.53  tff(c_772, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_769])).
% 3.58/1.53  tff(c_781, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_686, c_772])).
% 3.58/1.53  tff(c_783, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitLeft, [status(thm)], [c_781])).
% 3.58/1.53  tff(c_8, plain, (![B_4, A_3]: (v4_relat_1(B_4, A_3) | ~r1_tarski(k1_relat_1(B_4), A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.58/1.53  tff(c_788, plain, (![A_3]: (v4_relat_1('#skF_4', A_3) | ~r1_tarski('#skF_1', A_3) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_783, c_8])).
% 3.58/1.53  tff(c_808, plain, (![A_160]: (v4_relat_1('#skF_4', A_160) | ~r1_tarski('#skF_1', A_160))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_788])).
% 3.58/1.53  tff(c_12, plain, (![B_6, A_5]: (k7_relat_1(B_6, A_5)=B_6 | ~v4_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.58/1.53  tff(c_814, plain, (![A_160]: (k7_relat_1('#skF_4', A_160)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_160))), inference(resolution, [status(thm)], [c_808, c_12])).
% 3.58/1.53  tff(c_819, plain, (![A_161]: (k7_relat_1('#skF_4', A_161)='#skF_4' | ~r1_tarski('#skF_1', A_161))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_814])).
% 3.58/1.53  tff(c_828, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_40, c_819])).
% 3.58/1.53  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.58/1.53  tff(c_734, plain, (![A_146, B_147, C_148, D_149]: (k2_partfun1(A_146, B_147, C_148, D_149)=k7_relat_1(C_148, D_149) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))) | ~v1_funct_1(C_148))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.58/1.53  tff(c_736, plain, (![D_149]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_149)=k7_relat_1('#skF_4', D_149) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_734])).
% 3.58/1.53  tff(c_743, plain, (![D_149]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_149)=k7_relat_1('#skF_4', D_149))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_736])).
% 3.58/1.53  tff(c_38, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.58/1.53  tff(c_744, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_743, c_38])).
% 3.58/1.53  tff(c_829, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_828, c_744])).
% 3.58/1.53  tff(c_853, plain, (![A_168, B_169, C_170, D_171]: (r2_relset_1(A_168, B_169, C_170, C_170) | ~m1_subset_1(D_171, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.58/1.53  tff(c_863, plain, (![C_172]: (r2_relset_1('#skF_1', '#skF_2', C_172, C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_42, c_853])).
% 3.58/1.53  tff(c_865, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_863])).
% 3.58/1.53  tff(c_869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_829, c_865])).
% 3.58/1.53  tff(c_870, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_781])).
% 3.58/1.53  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.53  tff(c_893, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_870, c_870, c_4])).
% 3.58/1.53  tff(c_916, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_893, c_42])).
% 3.58/1.53  tff(c_94, plain, (![C_35, A_36, B_37]: (v4_relat_1(C_35, A_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.58/1.53  tff(c_100, plain, (![C_35, A_1]: (v4_relat_1(C_35, A_1) | ~m1_subset_1(C_35, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_94])).
% 3.58/1.53  tff(c_1030, plain, (![C_191, A_192]: (v4_relat_1(C_191, A_192) | ~m1_subset_1(C_191, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_870, c_100])).
% 3.58/1.53  tff(c_1039, plain, (![A_193]: (v4_relat_1('#skF_4', A_193))), inference(resolution, [status(thm)], [c_916, c_1030])).
% 3.58/1.53  tff(c_1042, plain, (![A_193]: (k7_relat_1('#skF_4', A_193)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1039, c_12])).
% 3.58/1.53  tff(c_1045, plain, (![A_193]: (k7_relat_1('#skF_4', A_193)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1042])).
% 3.58/1.53  tff(c_1046, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1045, c_744])).
% 3.58/1.53  tff(c_1051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_914, c_1046])).
% 3.58/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.53  
% 3.58/1.53  Inference rules
% 3.58/1.53  ----------------------
% 3.58/1.53  #Ref     : 0
% 3.58/1.53  #Sup     : 239
% 3.58/1.53  #Fact    : 0
% 3.58/1.53  #Define  : 0
% 3.58/1.53  #Split   : 6
% 3.58/1.53  #Chain   : 0
% 3.58/1.53  #Close   : 0
% 3.58/1.53  
% 3.58/1.53  Ordering : KBO
% 3.58/1.53  
% 3.58/1.53  Simplification rules
% 3.58/1.53  ----------------------
% 3.58/1.53  #Subsume      : 18
% 3.58/1.53  #Demod        : 223
% 3.58/1.53  #Tautology    : 125
% 3.58/1.53  #SimpNegUnit  : 4
% 3.58/1.53  #BackRed      : 87
% 3.58/1.53  
% 3.58/1.53  #Partial instantiations: 0
% 3.58/1.53  #Strategies tried      : 1
% 3.58/1.53  
% 3.58/1.53  Timing (in seconds)
% 3.58/1.53  ----------------------
% 3.58/1.54  Preprocessing        : 0.33
% 3.58/1.54  Parsing              : 0.17
% 3.58/1.54  CNF conversion       : 0.02
% 3.58/1.54  Main loop            : 0.43
% 3.58/1.54  Inferencing          : 0.15
% 3.58/1.54  Reduction            : 0.14
% 3.58/1.54  Demodulation         : 0.10
% 3.58/1.54  BG Simplification    : 0.02
% 3.58/1.54  Subsumption          : 0.07
% 3.58/1.54  Abstraction          : 0.02
% 3.58/1.54  MUC search           : 0.00
% 3.58/1.54  Cooper               : 0.00
% 3.58/1.54  Total                : 0.80
% 3.58/1.54  Index Insertion      : 0.00
% 3.58/1.54  Index Deletion       : 0.00
% 3.58/1.54  Index Matching       : 0.00
% 3.58/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
