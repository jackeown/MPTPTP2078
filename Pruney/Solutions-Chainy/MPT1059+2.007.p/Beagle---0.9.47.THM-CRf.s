%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:33 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 114 expanded)
%              Number of leaves         :   39 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 279 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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

tff(f_114,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_54,plain,(
    m1_subset_1('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_159,plain,(
    ! [C_74,B_75,A_76] :
      ( v5_relat_1(C_74,B_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_173,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_159])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_112,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_124,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_112])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_58,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_231,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_245,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_231])).

tff(c_422,plain,(
    ! [B_132,A_133,C_134] :
      ( k1_xboole_0 = B_132
      | k1_relset_1(A_133,B_132,C_134) = A_133
      | ~ v1_funct_2(C_134,A_133,B_132)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_425,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_422])).

tff(c_438,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_245,c_425])).

tff(c_442,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_438])).

tff(c_462,plain,(
    ! [A_137,B_138,C_139] :
      ( k7_partfun1(A_137,B_138,C_139) = k1_funct_1(B_138,C_139)
      | ~ r2_hidden(C_139,k1_relat_1(B_138))
      | ~ v1_funct_1(B_138)
      | ~ v5_relat_1(B_138,A_137)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_464,plain,(
    ! [A_137,C_139] :
      ( k7_partfun1(A_137,'#skF_6',C_139) = k1_funct_1('#skF_6',C_139)
      | ~ r2_hidden(C_139,'#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_137)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_462])).

tff(c_475,plain,(
    ! [A_140,C_141] :
      ( k7_partfun1(A_140,'#skF_6',C_141) = k1_funct_1('#skF_6',C_141)
      | ~ r2_hidden(C_141,'#skF_4')
      | ~ v5_relat_1('#skF_6',A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_60,c_464])).

tff(c_480,plain,(
    ! [A_140,A_9] :
      ( k7_partfun1(A_140,'#skF_6',A_9) = k1_funct_1('#skF_6',A_9)
      | ~ v5_relat_1('#skF_6',A_140)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_9,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_475])).

tff(c_500,plain,(
    ! [A_143,A_144] :
      ( k7_partfun1(A_143,'#skF_6',A_144) = k1_funct_1('#skF_6',A_144)
      | ~ v5_relat_1('#skF_6',A_143)
      | ~ m1_subset_1(A_144,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_480])).

tff(c_504,plain,(
    ! [A_145] :
      ( k7_partfun1('#skF_5','#skF_6',A_145) = k1_funct_1('#skF_6',A_145)
      | ~ m1_subset_1(A_145,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_173,c_500])).

tff(c_508,plain,(
    k7_partfun1('#skF_5','#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_504])).

tff(c_52,plain,(
    k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_7') != k7_partfun1('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_509,plain,(
    k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_7') != k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_52])).

tff(c_535,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( k3_funct_2(A_151,B_152,C_153,D_154) = k1_funct_1(C_153,D_154)
      | ~ m1_subset_1(D_154,A_151)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ v1_funct_2(C_153,A_151,B_152)
      | ~ v1_funct_1(C_153)
      | v1_xboole_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_543,plain,(
    ! [B_152,C_153] :
      ( k3_funct_2('#skF_4',B_152,C_153,'#skF_7') = k1_funct_1(C_153,'#skF_7')
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_152)))
      | ~ v1_funct_2(C_153,'#skF_4',B_152)
      | ~ v1_funct_1(C_153)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_535])).

tff(c_550,plain,(
    ! [B_155,C_156] :
      ( k3_funct_2('#skF_4',B_155,C_156,'#skF_7') = k1_funct_1(C_156,'#skF_7')
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_155)))
      | ~ v1_funct_2(C_156,'#skF_4',B_155)
      | ~ v1_funct_1(C_156) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_543])).

tff(c_553,plain,
    ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_7')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_550])).

tff(c_564,plain,(
    k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_553])).

tff(c_566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_564])).

tff(c_567,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_438])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_97,plain,(
    ! [A_62] :
      ( v1_xboole_0(A_62)
      | r2_hidden('#skF_1'(A_62),A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_106,plain,(
    ! [A_63] :
      ( ~ r1_tarski(A_63,'#skF_1'(A_63))
      | v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_97,c_20])).

tff(c_111,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_590,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_111])).

tff(c_598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_590])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n003.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 17:48:42 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.43  
% 2.94/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3
% 2.94/1.44  
% 2.94/1.44  %Foreground sorts:
% 2.94/1.44  
% 2.94/1.44  
% 2.94/1.44  %Background operators:
% 2.94/1.44  
% 2.94/1.44  
% 2.94/1.44  %Foreground operators:
% 2.94/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.94/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.94/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.94/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.94/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.94/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.44  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.94/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.94/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.94/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.94/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.94/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.94/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.94/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.94/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.94/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.94/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.94/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.94/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.94/1.44  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.94/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.94/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.44  
% 2.94/1.45  tff(f_147, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 2.94/1.45  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.94/1.45  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.94/1.45  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.94/1.45  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.94/1.45  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.94/1.45  tff(f_114, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 2.94/1.45  tff(f_127, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.94/1.45  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.94/1.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.94/1.45  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.94/1.45  tff(c_62, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.94/1.45  tff(c_54, plain, (m1_subset_1('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.94/1.45  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.94/1.45  tff(c_159, plain, (![C_74, B_75, A_76]: (v5_relat_1(C_74, B_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.94/1.45  tff(c_173, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_159])).
% 2.94/1.45  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.94/1.45  tff(c_16, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.94/1.45  tff(c_112, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.94/1.45  tff(c_124, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_112])).
% 2.94/1.45  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.94/1.45  tff(c_58, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.94/1.45  tff(c_231, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.94/1.45  tff(c_245, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_231])).
% 2.94/1.45  tff(c_422, plain, (![B_132, A_133, C_134]: (k1_xboole_0=B_132 | k1_relset_1(A_133, B_132, C_134)=A_133 | ~v1_funct_2(C_134, A_133, B_132) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.94/1.45  tff(c_425, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_422])).
% 2.94/1.45  tff(c_438, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_245, c_425])).
% 2.94/1.45  tff(c_442, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_438])).
% 2.94/1.45  tff(c_462, plain, (![A_137, B_138, C_139]: (k7_partfun1(A_137, B_138, C_139)=k1_funct_1(B_138, C_139) | ~r2_hidden(C_139, k1_relat_1(B_138)) | ~v1_funct_1(B_138) | ~v5_relat_1(B_138, A_137) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.94/1.45  tff(c_464, plain, (![A_137, C_139]: (k7_partfun1(A_137, '#skF_6', C_139)=k1_funct_1('#skF_6', C_139) | ~r2_hidden(C_139, '#skF_4') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_137) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_442, c_462])).
% 2.94/1.45  tff(c_475, plain, (![A_140, C_141]: (k7_partfun1(A_140, '#skF_6', C_141)=k1_funct_1('#skF_6', C_141) | ~r2_hidden(C_141, '#skF_4') | ~v5_relat_1('#skF_6', A_140))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_60, c_464])).
% 2.94/1.45  tff(c_480, plain, (![A_140, A_9]: (k7_partfun1(A_140, '#skF_6', A_9)=k1_funct_1('#skF_6', A_9) | ~v5_relat_1('#skF_6', A_140) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_9, '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_475])).
% 2.94/1.45  tff(c_500, plain, (![A_143, A_144]: (k7_partfun1(A_143, '#skF_6', A_144)=k1_funct_1('#skF_6', A_144) | ~v5_relat_1('#skF_6', A_143) | ~m1_subset_1(A_144, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_480])).
% 2.94/1.45  tff(c_504, plain, (![A_145]: (k7_partfun1('#skF_5', '#skF_6', A_145)=k1_funct_1('#skF_6', A_145) | ~m1_subset_1(A_145, '#skF_4'))), inference(resolution, [status(thm)], [c_173, c_500])).
% 2.94/1.45  tff(c_508, plain, (k7_partfun1('#skF_5', '#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_504])).
% 2.94/1.45  tff(c_52, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k7_partfun1('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.94/1.45  tff(c_509, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_508, c_52])).
% 2.94/1.45  tff(c_535, plain, (![A_151, B_152, C_153, D_154]: (k3_funct_2(A_151, B_152, C_153, D_154)=k1_funct_1(C_153, D_154) | ~m1_subset_1(D_154, A_151) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~v1_funct_2(C_153, A_151, B_152) | ~v1_funct_1(C_153) | v1_xboole_0(A_151))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.94/1.45  tff(c_543, plain, (![B_152, C_153]: (k3_funct_2('#skF_4', B_152, C_153, '#skF_7')=k1_funct_1(C_153, '#skF_7') | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_152))) | ~v1_funct_2(C_153, '#skF_4', B_152) | ~v1_funct_1(C_153) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_535])).
% 2.94/1.45  tff(c_550, plain, (![B_155, C_156]: (k3_funct_2('#skF_4', B_155, C_156, '#skF_7')=k1_funct_1(C_156, '#skF_7') | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_155))) | ~v1_funct_2(C_156, '#skF_4', B_155) | ~v1_funct_1(C_156))), inference(negUnitSimplification, [status(thm)], [c_64, c_543])).
% 2.94/1.45  tff(c_553, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_7') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_550])).
% 2.94/1.45  tff(c_564, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_553])).
% 2.94/1.45  tff(c_566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_509, c_564])).
% 2.94/1.45  tff(c_567, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_438])).
% 2.94/1.45  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.94/1.45  tff(c_97, plain, (![A_62]: (v1_xboole_0(A_62) | r2_hidden('#skF_1'(A_62), A_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.45  tff(c_20, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.94/1.45  tff(c_106, plain, (![A_63]: (~r1_tarski(A_63, '#skF_1'(A_63)) | v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_97, c_20])).
% 2.94/1.45  tff(c_111, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_106])).
% 2.94/1.45  tff(c_590, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_567, c_111])).
% 2.94/1.45  tff(c_598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_590])).
% 2.94/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.45  
% 2.94/1.45  Inference rules
% 2.94/1.45  ----------------------
% 2.94/1.45  #Ref     : 0
% 2.94/1.45  #Sup     : 110
% 2.94/1.45  #Fact    : 0
% 2.94/1.45  #Define  : 0
% 2.94/1.45  #Split   : 5
% 2.94/1.45  #Chain   : 0
% 2.94/1.45  #Close   : 0
% 2.94/1.45  
% 2.94/1.45  Ordering : KBO
% 2.94/1.45  
% 2.94/1.45  Simplification rules
% 2.94/1.45  ----------------------
% 2.94/1.45  #Subsume      : 20
% 2.94/1.45  #Demod        : 84
% 2.94/1.45  #Tautology    : 44
% 2.94/1.45  #SimpNegUnit  : 8
% 3.05/1.45  #BackRed      : 30
% 3.05/1.45  
% 3.05/1.45  #Partial instantiations: 0
% 3.05/1.45  #Strategies tried      : 1
% 3.05/1.45  
% 3.05/1.45  Timing (in seconds)
% 3.05/1.45  ----------------------
% 3.05/1.45  Preprocessing        : 0.35
% 3.05/1.46  Parsing              : 0.19
% 3.05/1.46  CNF conversion       : 0.02
% 3.05/1.46  Main loop            : 0.31
% 3.05/1.46  Inferencing          : 0.11
% 3.05/1.46  Reduction            : 0.10
% 3.05/1.46  Demodulation         : 0.07
% 3.05/1.46  BG Simplification    : 0.02
% 3.05/1.46  Subsumption          : 0.06
% 3.05/1.46  Abstraction          : 0.01
% 3.05/1.46  MUC search           : 0.00
% 3.05/1.46  Cooper               : 0.00
% 3.05/1.46  Total                : 0.70
% 3.05/1.46  Index Insertion      : 0.00
% 3.05/1.46  Index Deletion       : 0.00
% 3.05/1.46  Index Matching       : 0.00
% 3.05/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
