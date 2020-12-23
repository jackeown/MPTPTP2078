%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:41 EST 2020

% Result     : Theorem 4.96s
% Output     : CNFRefutation 4.96s
% Verified   : 
% Statistics : Number of formulae       :  175 (1379 expanded)
%              Number of leaves         :   32 ( 457 expanded)
%              Depth                    :   16
%              Number of atoms          :  347 (4143 expanded)
%              Number of equality atoms :  149 (1159 expanded)
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

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_121,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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

tff(f_70,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_151,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_157,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_151])).

tff(c_164,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_157])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_214,plain,(
    ! [A_55,B_56,D_57] :
      ( r2_relset_1(A_55,B_56,D_57,D_57)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_228,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_214])).

tff(c_244,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_262,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_244])).

tff(c_406,plain,(
    ! [B_93,A_94,C_95] :
      ( k1_xboole_0 = B_93
      | k1_relset_1(A_94,B_93,C_95) = A_94
      | ~ v1_funct_2(C_95,A_94,B_93)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_413,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_406])).

tff(c_426,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_262,c_413])).

tff(c_431,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_160,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_151])).

tff(c_167,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_160])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_263,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_244])).

tff(c_416,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_406])).

tff(c_429,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_263,c_416])).

tff(c_437,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_514,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_1'(A_104,B_105),k1_relat_1(A_104))
      | B_105 = A_104
      | k1_relat_1(B_105) != k1_relat_1(A_104)
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105)
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_517,plain,(
    ! [B_105] :
      ( r2_hidden('#skF_1'('#skF_4',B_105),'#skF_2')
      | B_105 = '#skF_4'
      | k1_relat_1(B_105) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_514])).

tff(c_597,plain,(
    ! [B_118] :
      ( r2_hidden('#skF_1'('#skF_4',B_118),'#skF_2')
      | B_118 = '#skF_4'
      | k1_relat_1(B_118) != '#skF_2'
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_60,c_437,c_517])).

tff(c_48,plain,(
    ! [E_33] :
      ( k1_funct_1('#skF_5',E_33) = k1_funct_1('#skF_4',E_33)
      | ~ r2_hidden(E_33,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_808,plain,(
    ! [B_137] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_137)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_137))
      | B_137 = '#skF_4'
      | k1_relat_1(B_137) != '#skF_2'
      | ~ v1_funct_1(B_137)
      | ~ v1_relat_1(B_137) ) ),
    inference(resolution,[status(thm)],[c_597,c_48])).

tff(c_24,plain,(
    ! [B_17,A_13] :
      ( k1_funct_1(B_17,'#skF_1'(A_13,B_17)) != k1_funct_1(A_13,'#skF_1'(A_13,B_17))
      | B_17 = A_13
      | k1_relat_1(B_17) != k1_relat_1(A_13)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_815,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_24])).

tff(c_822,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_54,c_431,c_167,c_60,c_437,c_431,c_815])).

tff(c_46,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_835,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_822,c_46])).

tff(c_846,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_835])).

tff(c_847,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_878,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_877,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_847,c_12])).

tff(c_96,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_103,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_96])).

tff(c_110,plain,(
    ! [B_44,A_45] :
      ( B_44 = A_45
      | ~ r1_tarski(B_44,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_110])).

tff(c_213,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_937,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_213])).

tff(c_945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_937])).

tff(c_946,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_974,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_946,c_8])).

tff(c_973,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_946,c_946,c_12])).

tff(c_1042,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_213])).

tff(c_1050,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_1042])).

tff(c_1051,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_1056,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1051,c_50])).

tff(c_1195,plain,(
    ! [A_174,B_175,C_176] :
      ( k1_relset_1(A_174,B_175,C_176) = k1_relat_1(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1236,plain,(
    ! [C_182] :
      ( k1_relset_1('#skF_2','#skF_3',C_182) = k1_relat_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1051,c_1195])).

tff(c_1248,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1056,c_1236])).

tff(c_1312,plain,(
    ! [B_189,C_190,A_191] :
      ( k1_xboole_0 = B_189
      | v1_funct_2(C_190,A_191,B_189)
      | k1_relset_1(A_191,B_189,C_190) != A_191
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_191,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1315,plain,(
    ! [C_190] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(C_190,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',C_190) != '#skF_2'
      | ~ m1_subset_1(C_190,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1051,c_1312])).

tff(c_1407,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1315])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1062,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1051,c_10])).

tff(c_1112,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1062])).

tff(c_1424,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_1112])).

tff(c_1431,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_1407,c_12])).

tff(c_1460,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_1051])).

tff(c_1462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1424,c_1460])).

tff(c_1464,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1315])).

tff(c_1481,plain,(
    ! [B_207,A_208,C_209] :
      ( k1_xboole_0 = B_207
      | k1_relset_1(A_208,B_207,C_209) = A_208
      | ~ v1_funct_2(C_209,A_208,B_207)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_208,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1484,plain,(
    ! [C_209] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_209) = '#skF_2'
      | ~ v1_funct_2(C_209,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_209,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1051,c_1481])).

tff(c_1499,plain,(
    ! [C_211] :
      ( k1_relset_1('#skF_2','#skF_3',C_211) = '#skF_2'
      | ~ v1_funct_2(C_211,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_211,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1464,c_1484])).

tff(c_1505,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1056,c_1499])).

tff(c_1515,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1248,c_1505])).

tff(c_1057,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1051,c_56])).

tff(c_1247,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1057,c_1236])).

tff(c_1502,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1057,c_1499])).

tff(c_1512,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1247,c_1502])).

tff(c_1723,plain,(
    ! [A_229,B_230] :
      ( r2_hidden('#skF_1'(A_229,B_230),k1_relat_1(A_229))
      | B_230 = A_229
      | k1_relat_1(B_230) != k1_relat_1(A_229)
      | ~ v1_funct_1(B_230)
      | ~ v1_relat_1(B_230)
      | ~ v1_funct_1(A_229)
      | ~ v1_relat_1(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1729,plain,(
    ! [B_230] :
      ( r2_hidden('#skF_1'('#skF_4',B_230),'#skF_2')
      | B_230 = '#skF_4'
      | k1_relat_1(B_230) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_230)
      | ~ v1_relat_1(B_230)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1512,c_1723])).

tff(c_1824,plain,(
    ! [B_237] :
      ( r2_hidden('#skF_1'('#skF_4',B_237),'#skF_2')
      | B_237 = '#skF_4'
      | k1_relat_1(B_237) != '#skF_2'
      | ~ v1_funct_1(B_237)
      | ~ v1_relat_1(B_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_60,c_1512,c_1729])).

tff(c_1849,plain,(
    ! [B_241] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_241)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_241))
      | B_241 = '#skF_4'
      | k1_relat_1(B_241) != '#skF_2'
      | ~ v1_funct_1(B_241)
      | ~ v1_relat_1(B_241) ) ),
    inference(resolution,[status(thm)],[c_1824,c_48])).

tff(c_1856,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1849,c_24])).

tff(c_1863,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_54,c_1515,c_167,c_60,c_1515,c_1512,c_1856])).

tff(c_104,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_96])).

tff(c_119,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_110])).

tff(c_190,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_1053,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1051,c_190])).

tff(c_1882,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_1053])).

tff(c_1895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1882])).

tff(c_1897,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1062])).

tff(c_1916,plain,(
    ! [A_3] : r1_tarski('#skF_5',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1897,c_8])).

tff(c_1925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1916,c_1053])).

tff(c_1926,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_1930,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1926,c_50])).

tff(c_2038,plain,(
    ! [A_260,B_261,C_262] :
      ( k1_relset_1(A_260,B_261,C_262) = k1_relat_1(C_262)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2072,plain,(
    ! [C_270] :
      ( k1_relset_1('#skF_2','#skF_3',C_270) = k1_relat_1(C_270)
      | ~ m1_subset_1(C_270,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1926,c_2038])).

tff(c_2083,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1930,c_2072])).

tff(c_2172,plain,(
    ! [B_280,C_281,A_282] :
      ( k1_xboole_0 = B_280
      | v1_funct_2(C_281,A_282,B_280)
      | k1_relset_1(A_282,B_280,C_281) != A_282
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_282,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2175,plain,(
    ! [C_281] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(C_281,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',C_281) != '#skF_2'
      | ~ m1_subset_1(C_281,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1926,c_2172])).

tff(c_2273,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2175])).

tff(c_1936,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1926,c_10])).

tff(c_1983,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1936])).

tff(c_2289,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2273,c_1983])).

tff(c_2336,plain,(
    ! [A_301] : k2_zfmisc_1(A_301,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2273,c_2273,c_12])).

tff(c_2359,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2336,c_1926])).

tff(c_2371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2289,c_2359])).

tff(c_2373,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2175])).

tff(c_2488,plain,(
    ! [B_315,A_316,C_317] :
      ( k1_xboole_0 = B_315
      | k1_relset_1(A_316,B_315,C_317) = A_316
      | ~ v1_funct_2(C_317,A_316,B_315)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_316,B_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2491,plain,(
    ! [C_317] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_317) = '#skF_2'
      | ~ v1_funct_2(C_317,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_317,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1926,c_2488])).

tff(c_2505,plain,(
    ! [C_318] :
      ( k1_relset_1('#skF_2','#skF_3',C_318) = '#skF_2'
      | ~ v1_funct_2(C_318,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_318,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2373,c_2491])).

tff(c_2508,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1930,c_2505])).

tff(c_2518,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2083,c_2508])).

tff(c_1931,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1926,c_56])).

tff(c_2084,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1931,c_2072])).

tff(c_2511,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1931,c_2505])).

tff(c_2521,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2084,c_2511])).

tff(c_2745,plain,(
    ! [A_334,B_335] :
      ( r2_hidden('#skF_1'(A_334,B_335),k1_relat_1(A_334))
      | B_335 = A_334
      | k1_relat_1(B_335) != k1_relat_1(A_334)
      | ~ v1_funct_1(B_335)
      | ~ v1_relat_1(B_335)
      | ~ v1_funct_1(A_334)
      | ~ v1_relat_1(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2748,plain,(
    ! [B_335] :
      ( r2_hidden('#skF_1'('#skF_4',B_335),'#skF_2')
      | B_335 = '#skF_4'
      | k1_relat_1(B_335) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_335)
      | ~ v1_relat_1(B_335)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2521,c_2745])).

tff(c_2756,plain,(
    ! [B_336] :
      ( r2_hidden('#skF_1'('#skF_4',B_336),'#skF_2')
      | B_336 = '#skF_4'
      | k1_relat_1(B_336) != '#skF_2'
      | ~ v1_funct_1(B_336)
      | ~ v1_relat_1(B_336) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_60,c_2521,c_2748])).

tff(c_2760,plain,(
    ! [B_336] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_336)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_336))
      | B_336 = '#skF_4'
      | k1_relat_1(B_336) != '#skF_2'
      | ~ v1_funct_1(B_336)
      | ~ v1_relat_1(B_336) ) ),
    inference(resolution,[status(thm)],[c_2756,c_48])).

tff(c_2789,plain,(
    ! [B_340,A_341] :
      ( k1_funct_1(B_340,'#skF_1'(A_341,B_340)) != k1_funct_1(A_341,'#skF_1'(A_341,B_340))
      | B_340 = A_341
      | k1_relat_1(B_340) != k1_relat_1(A_341)
      | ~ v1_funct_1(B_340)
      | ~ v1_relat_1(B_340)
      | ~ v1_funct_1(A_341)
      | ~ v1_relat_1(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2796,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2760,c_2789])).

tff(c_2801,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_54,c_2518,c_167,c_60,c_2521,c_2518,c_2796])).

tff(c_1981,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1926,c_1926,c_120])).

tff(c_1982,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1981])).

tff(c_2808,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2801,c_1982])).

tff(c_2821,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2808])).

tff(c_2823,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1936])).

tff(c_2839,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2823,c_8])).

tff(c_2848,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2839,c_1982])).

tff(c_2849,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1981])).

tff(c_1929,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1926,c_103])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1945,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1929,c_2])).

tff(c_1980,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1945])).

tff(c_2869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2849,c_1980])).

tff(c_2870,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1945])).

tff(c_2876,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2870,c_46])).

tff(c_1957,plain,(
    ! [A_243,B_244,D_245] :
      ( r2_relset_1(A_243,B_244,D_245,D_245)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2944,plain,(
    ! [D_361] :
      ( r2_relset_1('#skF_2','#skF_3',D_361,D_361)
      | ~ m1_subset_1(D_361,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1926,c_1957])).

tff(c_2946,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1931,c_2944])).

tff(c_2953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2876,c_2946])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.96/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/2.04  
% 4.96/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/2.04  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.96/2.04  
% 4.96/2.04  %Foreground sorts:
% 4.96/2.04  
% 4.96/2.04  
% 4.96/2.04  %Background operators:
% 4.96/2.04  
% 4.96/2.04  
% 4.96/2.04  %Foreground operators:
% 4.96/2.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.96/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.96/2.04  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.96/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.96/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.96/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.96/2.04  tff('#skF_5', type, '#skF_5': $i).
% 4.96/2.04  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.96/2.04  tff('#skF_2', type, '#skF_2': $i).
% 4.96/2.04  tff('#skF_3', type, '#skF_3': $i).
% 4.96/2.04  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.96/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.96/2.04  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.96/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.96/2.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.96/2.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.96/2.04  tff('#skF_4', type, '#skF_4': $i).
% 4.96/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.96/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.96/2.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.96/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.96/2.04  
% 4.96/2.07  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.96/2.07  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.96/2.07  tff(f_121, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 4.96/2.07  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.96/2.07  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.96/2.07  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.96/2.07  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.96/2.07  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 4.96/2.07  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.96/2.07  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.96/2.07  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.96/2.07  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.96/2.07  tff(c_22, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.96/2.07  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.96/2.07  tff(c_151, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.96/2.07  tff(c_157, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_151])).
% 4.96/2.07  tff(c_164, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_157])).
% 4.96/2.07  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.96/2.07  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.96/2.07  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.96/2.07  tff(c_214, plain, (![A_55, B_56, D_57]: (r2_relset_1(A_55, B_56, D_57, D_57) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.96/2.07  tff(c_228, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_214])).
% 4.96/2.07  tff(c_244, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.96/2.07  tff(c_262, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_244])).
% 4.96/2.07  tff(c_406, plain, (![B_93, A_94, C_95]: (k1_xboole_0=B_93 | k1_relset_1(A_94, B_93, C_95)=A_94 | ~v1_funct_2(C_95, A_94, B_93) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.96/2.07  tff(c_413, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_406])).
% 4.96/2.07  tff(c_426, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_262, c_413])).
% 4.96/2.07  tff(c_431, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_426])).
% 4.96/2.07  tff(c_160, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_151])).
% 4.96/2.07  tff(c_167, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_160])).
% 4.96/2.07  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.96/2.07  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.96/2.07  tff(c_263, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_244])).
% 4.96/2.07  tff(c_416, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_406])).
% 4.96/2.07  tff(c_429, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_263, c_416])).
% 4.96/2.07  tff(c_437, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_429])).
% 4.96/2.07  tff(c_514, plain, (![A_104, B_105]: (r2_hidden('#skF_1'(A_104, B_105), k1_relat_1(A_104)) | B_105=A_104 | k1_relat_1(B_105)!=k1_relat_1(A_104) | ~v1_funct_1(B_105) | ~v1_relat_1(B_105) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.96/2.07  tff(c_517, plain, (![B_105]: (r2_hidden('#skF_1'('#skF_4', B_105), '#skF_2') | B_105='#skF_4' | k1_relat_1(B_105)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_105) | ~v1_relat_1(B_105) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_437, c_514])).
% 4.96/2.07  tff(c_597, plain, (![B_118]: (r2_hidden('#skF_1'('#skF_4', B_118), '#skF_2') | B_118='#skF_4' | k1_relat_1(B_118)!='#skF_2' | ~v1_funct_1(B_118) | ~v1_relat_1(B_118))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_60, c_437, c_517])).
% 4.96/2.07  tff(c_48, plain, (![E_33]: (k1_funct_1('#skF_5', E_33)=k1_funct_1('#skF_4', E_33) | ~r2_hidden(E_33, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.96/2.07  tff(c_808, plain, (![B_137]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_137))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_137)) | B_137='#skF_4' | k1_relat_1(B_137)!='#skF_2' | ~v1_funct_1(B_137) | ~v1_relat_1(B_137))), inference(resolution, [status(thm)], [c_597, c_48])).
% 4.96/2.07  tff(c_24, plain, (![B_17, A_13]: (k1_funct_1(B_17, '#skF_1'(A_13, B_17))!=k1_funct_1(A_13, '#skF_1'(A_13, B_17)) | B_17=A_13 | k1_relat_1(B_17)!=k1_relat_1(A_13) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.96/2.07  tff(c_815, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_808, c_24])).
% 4.96/2.07  tff(c_822, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_54, c_431, c_167, c_60, c_437, c_431, c_815])).
% 4.96/2.07  tff(c_46, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.96/2.07  tff(c_835, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_822, c_46])).
% 4.96/2.07  tff(c_846, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_228, c_835])).
% 4.96/2.07  tff(c_847, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_429])).
% 4.96/2.07  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.96/2.07  tff(c_878, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_847, c_8])).
% 4.96/2.07  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.96/2.07  tff(c_877, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_847, c_847, c_12])).
% 4.96/2.07  tff(c_96, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.96/2.07  tff(c_103, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_96])).
% 4.96/2.07  tff(c_110, plain, (![B_44, A_45]: (B_44=A_45 | ~r1_tarski(B_44, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.96/2.07  tff(c_120, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_103, c_110])).
% 4.96/2.07  tff(c_213, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_120])).
% 4.96/2.07  tff(c_937, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_877, c_213])).
% 4.96/2.07  tff(c_945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_878, c_937])).
% 4.96/2.07  tff(c_946, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_426])).
% 4.96/2.07  tff(c_974, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_946, c_8])).
% 4.96/2.07  tff(c_973, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_946, c_946, c_12])).
% 4.96/2.07  tff(c_1042, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_973, c_213])).
% 4.96/2.07  tff(c_1050, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_974, c_1042])).
% 4.96/2.07  tff(c_1051, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_120])).
% 4.96/2.07  tff(c_1056, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1051, c_50])).
% 4.96/2.07  tff(c_1195, plain, (![A_174, B_175, C_176]: (k1_relset_1(A_174, B_175, C_176)=k1_relat_1(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.96/2.07  tff(c_1236, plain, (![C_182]: (k1_relset_1('#skF_2', '#skF_3', C_182)=k1_relat_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1051, c_1195])).
% 4.96/2.07  tff(c_1248, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1056, c_1236])).
% 4.96/2.07  tff(c_1312, plain, (![B_189, C_190, A_191]: (k1_xboole_0=B_189 | v1_funct_2(C_190, A_191, B_189) | k1_relset_1(A_191, B_189, C_190)!=A_191 | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_191, B_189))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.96/2.07  tff(c_1315, plain, (![C_190]: (k1_xboole_0='#skF_3' | v1_funct_2(C_190, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', C_190)!='#skF_2' | ~m1_subset_1(C_190, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1051, c_1312])).
% 4.96/2.07  tff(c_1407, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1315])).
% 4.96/2.07  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.96/2.07  tff(c_1062, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1051, c_10])).
% 4.96/2.07  tff(c_1112, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_1062])).
% 4.96/2.07  tff(c_1424, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1407, c_1112])).
% 4.96/2.07  tff(c_1431, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1407, c_1407, c_12])).
% 4.96/2.07  tff(c_1460, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1431, c_1051])).
% 4.96/2.07  tff(c_1462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1424, c_1460])).
% 4.96/2.07  tff(c_1464, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1315])).
% 4.96/2.07  tff(c_1481, plain, (![B_207, A_208, C_209]: (k1_xboole_0=B_207 | k1_relset_1(A_208, B_207, C_209)=A_208 | ~v1_funct_2(C_209, A_208, B_207) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_208, B_207))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.96/2.07  tff(c_1484, plain, (![C_209]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_209)='#skF_2' | ~v1_funct_2(C_209, '#skF_2', '#skF_3') | ~m1_subset_1(C_209, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1051, c_1481])).
% 4.96/2.07  tff(c_1499, plain, (![C_211]: (k1_relset_1('#skF_2', '#skF_3', C_211)='#skF_2' | ~v1_funct_2(C_211, '#skF_2', '#skF_3') | ~m1_subset_1(C_211, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_1464, c_1484])).
% 4.96/2.07  tff(c_1505, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1056, c_1499])).
% 4.96/2.07  tff(c_1515, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1248, c_1505])).
% 4.96/2.07  tff(c_1057, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1051, c_56])).
% 4.96/2.07  tff(c_1247, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1057, c_1236])).
% 4.96/2.07  tff(c_1502, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1057, c_1499])).
% 4.96/2.07  tff(c_1512, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1247, c_1502])).
% 4.96/2.07  tff(c_1723, plain, (![A_229, B_230]: (r2_hidden('#skF_1'(A_229, B_230), k1_relat_1(A_229)) | B_230=A_229 | k1_relat_1(B_230)!=k1_relat_1(A_229) | ~v1_funct_1(B_230) | ~v1_relat_1(B_230) | ~v1_funct_1(A_229) | ~v1_relat_1(A_229))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.96/2.07  tff(c_1729, plain, (![B_230]: (r2_hidden('#skF_1'('#skF_4', B_230), '#skF_2') | B_230='#skF_4' | k1_relat_1(B_230)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_230) | ~v1_relat_1(B_230) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1512, c_1723])).
% 4.96/2.07  tff(c_1824, plain, (![B_237]: (r2_hidden('#skF_1'('#skF_4', B_237), '#skF_2') | B_237='#skF_4' | k1_relat_1(B_237)!='#skF_2' | ~v1_funct_1(B_237) | ~v1_relat_1(B_237))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_60, c_1512, c_1729])).
% 4.96/2.07  tff(c_1849, plain, (![B_241]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_241))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_241)) | B_241='#skF_4' | k1_relat_1(B_241)!='#skF_2' | ~v1_funct_1(B_241) | ~v1_relat_1(B_241))), inference(resolution, [status(thm)], [c_1824, c_48])).
% 4.96/2.07  tff(c_1856, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1849, c_24])).
% 4.96/2.07  tff(c_1863, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_54, c_1515, c_167, c_60, c_1515, c_1512, c_1856])).
% 4.96/2.07  tff(c_104, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_96])).
% 4.96/2.07  tff(c_119, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_104, c_110])).
% 4.96/2.07  tff(c_190, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_119])).
% 4.96/2.07  tff(c_1053, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1051, c_190])).
% 4.96/2.07  tff(c_1882, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_1053])).
% 4.96/2.07  tff(c_1895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1882])).
% 4.96/2.07  tff(c_1897, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1062])).
% 4.96/2.07  tff(c_1916, plain, (![A_3]: (r1_tarski('#skF_5', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1897, c_8])).
% 4.96/2.07  tff(c_1925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1916, c_1053])).
% 4.96/2.07  tff(c_1926, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_119])).
% 4.96/2.07  tff(c_1930, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1926, c_50])).
% 4.96/2.07  tff(c_2038, plain, (![A_260, B_261, C_262]: (k1_relset_1(A_260, B_261, C_262)=k1_relat_1(C_262) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.96/2.07  tff(c_2072, plain, (![C_270]: (k1_relset_1('#skF_2', '#skF_3', C_270)=k1_relat_1(C_270) | ~m1_subset_1(C_270, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1926, c_2038])).
% 4.96/2.07  tff(c_2083, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1930, c_2072])).
% 4.96/2.07  tff(c_2172, plain, (![B_280, C_281, A_282]: (k1_xboole_0=B_280 | v1_funct_2(C_281, A_282, B_280) | k1_relset_1(A_282, B_280, C_281)!=A_282 | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_282, B_280))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.96/2.07  tff(c_2175, plain, (![C_281]: (k1_xboole_0='#skF_3' | v1_funct_2(C_281, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', C_281)!='#skF_2' | ~m1_subset_1(C_281, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1926, c_2172])).
% 4.96/2.07  tff(c_2273, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2175])).
% 4.96/2.07  tff(c_1936, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1926, c_10])).
% 4.96/2.07  tff(c_1983, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_1936])).
% 4.96/2.07  tff(c_2289, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2273, c_1983])).
% 4.96/2.07  tff(c_2336, plain, (![A_301]: (k2_zfmisc_1(A_301, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2273, c_2273, c_12])).
% 4.96/2.07  tff(c_2359, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2336, c_1926])).
% 4.96/2.07  tff(c_2371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2289, c_2359])).
% 4.96/2.07  tff(c_2373, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2175])).
% 4.96/2.07  tff(c_2488, plain, (![B_315, A_316, C_317]: (k1_xboole_0=B_315 | k1_relset_1(A_316, B_315, C_317)=A_316 | ~v1_funct_2(C_317, A_316, B_315) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_316, B_315))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.96/2.07  tff(c_2491, plain, (![C_317]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_317)='#skF_2' | ~v1_funct_2(C_317, '#skF_2', '#skF_3') | ~m1_subset_1(C_317, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1926, c_2488])).
% 4.96/2.07  tff(c_2505, plain, (![C_318]: (k1_relset_1('#skF_2', '#skF_3', C_318)='#skF_2' | ~v1_funct_2(C_318, '#skF_2', '#skF_3') | ~m1_subset_1(C_318, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_2373, c_2491])).
% 4.96/2.07  tff(c_2508, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1930, c_2505])).
% 4.96/2.07  tff(c_2518, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2083, c_2508])).
% 4.96/2.07  tff(c_1931, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1926, c_56])).
% 4.96/2.07  tff(c_2084, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1931, c_2072])).
% 4.96/2.07  tff(c_2511, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1931, c_2505])).
% 4.96/2.07  tff(c_2521, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2084, c_2511])).
% 4.96/2.07  tff(c_2745, plain, (![A_334, B_335]: (r2_hidden('#skF_1'(A_334, B_335), k1_relat_1(A_334)) | B_335=A_334 | k1_relat_1(B_335)!=k1_relat_1(A_334) | ~v1_funct_1(B_335) | ~v1_relat_1(B_335) | ~v1_funct_1(A_334) | ~v1_relat_1(A_334))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.96/2.07  tff(c_2748, plain, (![B_335]: (r2_hidden('#skF_1'('#skF_4', B_335), '#skF_2') | B_335='#skF_4' | k1_relat_1(B_335)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_335) | ~v1_relat_1(B_335) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2521, c_2745])).
% 4.96/2.07  tff(c_2756, plain, (![B_336]: (r2_hidden('#skF_1'('#skF_4', B_336), '#skF_2') | B_336='#skF_4' | k1_relat_1(B_336)!='#skF_2' | ~v1_funct_1(B_336) | ~v1_relat_1(B_336))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_60, c_2521, c_2748])).
% 4.96/2.07  tff(c_2760, plain, (![B_336]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_336))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_336)) | B_336='#skF_4' | k1_relat_1(B_336)!='#skF_2' | ~v1_funct_1(B_336) | ~v1_relat_1(B_336))), inference(resolution, [status(thm)], [c_2756, c_48])).
% 4.96/2.07  tff(c_2789, plain, (![B_340, A_341]: (k1_funct_1(B_340, '#skF_1'(A_341, B_340))!=k1_funct_1(A_341, '#skF_1'(A_341, B_340)) | B_340=A_341 | k1_relat_1(B_340)!=k1_relat_1(A_341) | ~v1_funct_1(B_340) | ~v1_relat_1(B_340) | ~v1_funct_1(A_341) | ~v1_relat_1(A_341))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.96/2.07  tff(c_2796, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2760, c_2789])).
% 4.96/2.07  tff(c_2801, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_54, c_2518, c_167, c_60, c_2521, c_2518, c_2796])).
% 4.96/2.07  tff(c_1981, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1926, c_1926, c_120])).
% 4.96/2.07  tff(c_1982, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_1981])).
% 4.96/2.07  tff(c_2808, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2801, c_1982])).
% 4.96/2.07  tff(c_2821, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2808])).
% 4.96/2.07  tff(c_2823, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1936])).
% 4.96/2.07  tff(c_2839, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2823, c_8])).
% 4.96/2.07  tff(c_2848, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2839, c_1982])).
% 4.96/2.07  tff(c_2849, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_1981])).
% 4.96/2.07  tff(c_1929, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1926, c_103])).
% 4.96/2.07  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.96/2.07  tff(c_1945, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_1929, c_2])).
% 4.96/2.07  tff(c_1980, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_1945])).
% 4.96/2.07  tff(c_2869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2849, c_1980])).
% 4.96/2.07  tff(c_2870, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_1945])).
% 4.96/2.07  tff(c_2876, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2870, c_46])).
% 4.96/2.07  tff(c_1957, plain, (![A_243, B_244, D_245]: (r2_relset_1(A_243, B_244, D_245, D_245) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.96/2.07  tff(c_2944, plain, (![D_361]: (r2_relset_1('#skF_2', '#skF_3', D_361, D_361) | ~m1_subset_1(D_361, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1926, c_1957])).
% 4.96/2.07  tff(c_2946, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_1931, c_2944])).
% 4.96/2.07  tff(c_2953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2876, c_2946])).
% 4.96/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/2.07  
% 4.96/2.07  Inference rules
% 4.96/2.07  ----------------------
% 4.96/2.07  #Ref     : 3
% 4.96/2.07  #Sup     : 565
% 4.96/2.07  #Fact    : 0
% 4.96/2.07  #Define  : 0
% 4.96/2.07  #Split   : 16
% 4.96/2.07  #Chain   : 0
% 4.96/2.07  #Close   : 0
% 4.96/2.07  
% 4.96/2.07  Ordering : KBO
% 4.96/2.07  
% 4.96/2.07  Simplification rules
% 4.96/2.07  ----------------------
% 4.96/2.07  #Subsume      : 71
% 4.96/2.07  #Demod        : 846
% 4.96/2.07  #Tautology    : 368
% 4.96/2.07  #SimpNegUnit  : 47
% 4.96/2.07  #BackRed      : 206
% 4.96/2.07  
% 4.96/2.07  #Partial instantiations: 0
% 4.96/2.07  #Strategies tried      : 1
% 4.96/2.07  
% 4.96/2.07  Timing (in seconds)
% 4.96/2.07  ----------------------
% 4.96/2.07  Preprocessing        : 0.49
% 4.96/2.07  Parsing              : 0.28
% 4.96/2.07  CNF conversion       : 0.03
% 4.96/2.07  Main loop            : 0.75
% 4.96/2.07  Inferencing          : 0.27
% 4.96/2.07  Reduction            : 0.25
% 4.96/2.07  Demodulation         : 0.18
% 4.96/2.07  BG Simplification    : 0.03
% 4.96/2.07  Subsumption          : 0.13
% 4.96/2.07  Abstraction          : 0.04
% 4.96/2.07  MUC search           : 0.00
% 4.96/2.07  Cooper               : 0.00
% 4.96/2.07  Total                : 1.30
% 4.96/2.07  Index Insertion      : 0.00
% 4.96/2.07  Index Deletion       : 0.00
% 4.96/2.07  Index Matching       : 0.00
% 4.96/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
