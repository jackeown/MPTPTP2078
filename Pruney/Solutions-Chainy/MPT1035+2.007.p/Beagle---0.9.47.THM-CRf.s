%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:59 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :  166 (1006 expanded)
%              Number of leaves         :   32 ( 331 expanded)
%              Depth                    :   15
%              Number of atoms          :  346 (3647 expanded)
%              Number of equality atoms :   83 (1239 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ( B = k1_xboole_0
               => A = k1_xboole_0 )
             => ( r1_partfun1(C,D)
              <=> ! [E] :
                    ( r2_hidden(E,k1_relset_1(A,B,C))
                   => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_72,axiom,(
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

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
           => ( r1_partfun1(A,B)
            <=> ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_613,plain,(
    ! [B_138,A_139] :
      ( v1_relat_1(B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_139))
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_622,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_613])).

tff(c_629,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_622])).

tff(c_684,plain,(
    ! [C_152,A_153,B_154] :
      ( v4_relat_1(C_152,A_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_697,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_684])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,
    ( k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_72,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_78,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_87,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_78])).

tff(c_94,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_87])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_84,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_78])).

tff(c_91,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_84])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_111,plain,(
    ! [C_50,A_51,B_52] :
      ( v4_relat_1(C_50,A_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_124,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_111])).

tff(c_38,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_61,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_200,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_212,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_200])).

tff(c_277,plain,(
    ! [B_96,A_97,C_98] :
      ( k1_xboole_0 = B_96
      | k1_relset_1(A_97,B_96,C_98) = A_97
      | ~ v1_funct_2(C_98,A_97,B_96)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_284,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_277])).

tff(c_291,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_212,c_284])).

tff(c_292,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_291])).

tff(c_419,plain,(
    ! [A_111,B_112] :
      ( r2_hidden('#skF_1'(A_111,B_112),k1_relat_1(A_111))
      | r1_partfun1(A_111,B_112)
      | ~ r1_tarski(k1_relat_1(A_111),k1_relat_1(B_112))
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112)
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_213,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_200])).

tff(c_60,plain,(
    ! [E_36] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_108,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_60])).

tff(c_218,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_108])).

tff(c_423,plain,(
    ! [B_112] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_112)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_112))
      | r1_partfun1('#skF_4',B_112)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_112))
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_419,c_218])).

tff(c_440,plain,(
    ! [B_116] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_116)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_116))
      | r1_partfun1('#skF_4',B_116)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_116))
      | ~ v1_funct_1(B_116)
      | ~ v1_relat_1(B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_48,c_423])).

tff(c_443,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_440])).

tff(c_448,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_44,c_443])).

tff(c_449,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_448])).

tff(c_533,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_536,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_533])).

tff(c_540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_124,c_536])).

tff(c_542,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_541,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_596,plain,(
    ! [B_134,A_135] :
      ( k1_funct_1(B_134,'#skF_1'(A_135,B_134)) != k1_funct_1(A_135,'#skF_1'(A_135,B_134))
      | r1_partfun1(A_135,B_134)
      | ~ r1_tarski(k1_relat_1(A_135),k1_relat_1(B_134))
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134)
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_598,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_596])).

tff(c_601,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_48,c_91,c_44,c_542,c_292,c_598])).

tff(c_603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_601])).

tff(c_604,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_619,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_613])).

tff(c_626,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_619])).

tff(c_605,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_698,plain,(
    ! [A_155,B_156,C_157] :
      ( k1_relset_1(A_155,B_156,C_157) = k1_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_710,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_698])).

tff(c_849,plain,(
    ! [B_195,A_196,C_197] :
      ( k1_xboole_0 = B_195
      | k1_relset_1(A_196,B_195,C_197) = A_196
      | ~ v1_funct_2(C_197,A_196,B_195)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_196,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_856,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_849])).

tff(c_863,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_710,c_856])).

tff(c_864,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_863])).

tff(c_711,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_698])).

tff(c_52,plain,
    ( r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4'))
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_607,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_52])).

tff(c_716,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_607])).

tff(c_964,plain,(
    ! [B_209,C_210,A_211] :
      ( k1_funct_1(B_209,C_210) = k1_funct_1(A_211,C_210)
      | ~ r2_hidden(C_210,k1_relat_1(A_211))
      | ~ r1_partfun1(A_211,B_209)
      | ~ r1_tarski(k1_relat_1(A_211),k1_relat_1(B_209))
      | ~ v1_funct_1(B_209)
      | ~ v1_relat_1(B_209)
      | ~ v1_funct_1(A_211)
      | ~ v1_relat_1(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_970,plain,(
    ! [B_209] :
      ( k1_funct_1(B_209,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_209)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_209))
      | ~ v1_funct_1(B_209)
      | ~ v1_relat_1(B_209)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_716,c_964])).

tff(c_996,plain,(
    ! [B_212] :
      ( k1_funct_1(B_212,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_212)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_212))
      | ~ v1_funct_1(B_212)
      | ~ v1_relat_1(B_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_48,c_970])).

tff(c_999,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_864,c_996])).

tff(c_1004,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_44,c_605,c_999])).

tff(c_1005,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_604,c_1004])).

tff(c_1011,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_1005])).

tff(c_1015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_697,c_1011])).

tff(c_1017,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1016,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1022,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1017,c_1016])).

tff(c_1033,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_46])).

tff(c_1637,plain,(
    ! [B_319,A_320] :
      ( v1_relat_1(B_319)
      | ~ m1_subset_1(B_319,k1_zfmisc_1(A_320))
      | ~ v1_relat_1(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1646,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1033,c_1637])).

tff(c_1653,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1646])).

tff(c_1708,plain,(
    ! [C_333,A_334,B_335] :
      ( v4_relat_1(C_333,A_334)
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1721,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1033,c_1708])).

tff(c_1044,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_1050,plain,(
    ! [B_219,A_220] :
      ( v1_relat_1(B_219)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(A_220))
      | ~ v1_relat_1(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1059,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1033,c_1050])).

tff(c_1066,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1059])).

tff(c_1034,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_40])).

tff(c_1056,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1034,c_1050])).

tff(c_1063,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1056])).

tff(c_1085,plain,(
    ! [C_226,A_227,B_228] :
      ( v4_relat_1(C_226,A_227)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1098,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1033,c_1085])).

tff(c_1027,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_42])).

tff(c_1177,plain,(
    ! [A_250,B_251,C_252] :
      ( k1_relset_1(A_250,B_251,C_252) = k1_relat_1(C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1189,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1034,c_1177])).

tff(c_28,plain,(
    ! [B_17,C_18] :
      ( k1_relset_1(k1_xboole_0,B_17,C_18) = k1_xboole_0
      | ~ v1_funct_2(C_18,k1_xboole_0,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1289,plain,(
    ! [B_265,C_266] :
      ( k1_relset_1('#skF_3',B_265,C_266) = '#skF_3'
      | ~ v1_funct_2(C_266,'#skF_3',B_265)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_265))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1017,c_1017,c_1017,c_1017,c_28])).

tff(c_1296,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1034,c_1289])).

tff(c_1303,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_1189,c_1296])).

tff(c_1468,plain,(
    ! [A_287,B_288] :
      ( r2_hidden('#skF_1'(A_287,B_288),k1_relat_1(A_287))
      | r1_partfun1(A_287,B_288)
      | ~ r1_tarski(k1_relat_1(A_287),k1_relat_1(B_288))
      | ~ v1_funct_1(B_288)
      | ~ v1_relat_1(B_288)
      | ~ v1_funct_1(A_287)
      | ~ v1_relat_1(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1190,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1033,c_1177])).

tff(c_1081,plain,(
    ! [E_36] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_60])).

tff(c_1082,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1044,c_1081])).

tff(c_1195,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_1082])).

tff(c_1472,plain,(
    ! [B_288] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_288)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_288))
      | r1_partfun1('#skF_4',B_288)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_288))
      | ~ v1_funct_1(B_288)
      | ~ v1_relat_1(B_288)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1468,c_1195])).

tff(c_1573,plain,(
    ! [B_313] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_313)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_313))
      | r1_partfun1('#skF_4',B_313)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_313))
      | ~ v1_funct_1(B_313)
      | ~ v1_relat_1(B_313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_48,c_1472])).

tff(c_1576,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1303,c_1573])).

tff(c_1581,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_44,c_1576])).

tff(c_1582,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1044,c_1581])).

tff(c_1586,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1582])).

tff(c_1589,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_1586])).

tff(c_1593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_1098,c_1589])).

tff(c_1595,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1582])).

tff(c_1594,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1582])).

tff(c_1620,plain,(
    ! [B_315,A_316] :
      ( k1_funct_1(B_315,'#skF_1'(A_316,B_315)) != k1_funct_1(A_316,'#skF_1'(A_316,B_315))
      | r1_partfun1(A_316,B_315)
      | ~ r1_tarski(k1_relat_1(A_316),k1_relat_1(B_315))
      | ~ v1_funct_1(B_315)
      | ~ v1_relat_1(B_315)
      | ~ v1_funct_1(A_316)
      | ~ v1_relat_1(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1622,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1594,c_1620])).

tff(c_1625,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_48,c_1063,c_44,c_1595,c_1303,c_1622])).

tff(c_1627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1044,c_1625])).

tff(c_1628,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1643,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1034,c_1637])).

tff(c_1650,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1643])).

tff(c_1629,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1722,plain,(
    ! [A_336,B_337,C_338] :
      ( k1_relset_1(A_336,B_337,C_338) = k1_relat_1(C_338)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_336,B_337))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1734,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1034,c_1722])).

tff(c_1856,plain,(
    ! [B_361,C_362] :
      ( k1_relset_1('#skF_3',B_361,C_362) = '#skF_3'
      | ~ v1_funct_2(C_362,'#skF_3',B_361)
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_361))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1017,c_1017,c_1017,c_1017,c_28])).

tff(c_1863,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1034,c_1856])).

tff(c_1870,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_1734,c_1863])).

tff(c_1735,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1033,c_1722])).

tff(c_1631,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1629,c_1022,c_52])).

tff(c_1740,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1735,c_1631])).

tff(c_2139,plain,(
    ! [B_406,C_407,A_408] :
      ( k1_funct_1(B_406,C_407) = k1_funct_1(A_408,C_407)
      | ~ r2_hidden(C_407,k1_relat_1(A_408))
      | ~ r1_partfun1(A_408,B_406)
      | ~ r1_tarski(k1_relat_1(A_408),k1_relat_1(B_406))
      | ~ v1_funct_1(B_406)
      | ~ v1_relat_1(B_406)
      | ~ v1_funct_1(A_408)
      | ~ v1_relat_1(A_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2145,plain,(
    ! [B_406] :
      ( k1_funct_1(B_406,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_406)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_406))
      | ~ v1_funct_1(B_406)
      | ~ v1_relat_1(B_406)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1740,c_2139])).

tff(c_2152,plain,(
    ! [B_409] :
      ( k1_funct_1(B_409,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_409)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_409))
      | ~ v1_funct_1(B_409)
      | ~ v1_relat_1(B_409) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1653,c_48,c_2145])).

tff(c_2155,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1870,c_2152])).

tff(c_2160,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_44,c_1629,c_2155])).

tff(c_2161,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1628,c_2160])).

tff(c_2167,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_2161])).

tff(c_2171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1653,c_1721,c_2167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.03/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.73  
% 4.03/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.74  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.03/1.74  
% 4.03/1.74  %Foreground sorts:
% 4.03/1.74  
% 4.03/1.74  
% 4.03/1.74  %Background operators:
% 4.03/1.74  
% 4.03/1.74  
% 4.03/1.74  %Foreground operators:
% 4.03/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.03/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.03/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.03/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.03/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.03/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.03/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.03/1.74  tff('#skF_6', type, '#skF_6': $i).
% 4.03/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.03/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.03/1.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.03/1.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.03/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.03/1.74  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.03/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.03/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.03/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.03/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.03/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.03/1.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.03/1.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.03/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.03/1.74  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 4.03/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.03/1.74  
% 4.03/1.76  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.03/1.76  tff(f_113, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (r1_partfun1(C, D) <=> (![E]: (r2_hidden(E, k1_relset_1(A, B, C)) => (k1_funct_1(C, E) = k1_funct_1(D, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_2)).
% 4.03/1.76  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.03/1.76  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.03/1.76  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.03/1.76  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.03/1.76  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.03/1.76  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) => (r1_partfun1(A, B) <=> (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_partfun1)).
% 4.03/1.76  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.03/1.76  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.03/1.76  tff(c_613, plain, (![B_138, A_139]: (v1_relat_1(B_138) | ~m1_subset_1(B_138, k1_zfmisc_1(A_139)) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.03/1.76  tff(c_622, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_613])).
% 4.03/1.76  tff(c_629, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_622])).
% 4.03/1.76  tff(c_684, plain, (![C_152, A_153, B_154]: (v4_relat_1(C_152, A_153) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.03/1.76  tff(c_697, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_684])).
% 4.03/1.76  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.03/1.76  tff(c_50, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.03/1.76  tff(c_72, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_50])).
% 4.03/1.76  tff(c_78, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.03/1.76  tff(c_87, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_78])).
% 4.03/1.76  tff(c_94, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_87])).
% 4.03/1.76  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.03/1.76  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.03/1.76  tff(c_84, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_78])).
% 4.03/1.76  tff(c_91, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_84])).
% 4.03/1.76  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.03/1.76  tff(c_111, plain, (![C_50, A_51, B_52]: (v4_relat_1(C_50, A_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.03/1.76  tff(c_124, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_111])).
% 4.03/1.76  tff(c_38, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.03/1.76  tff(c_61, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_38])).
% 4.03/1.76  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.03/1.76  tff(c_200, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.03/1.76  tff(c_212, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_200])).
% 4.03/1.76  tff(c_277, plain, (![B_96, A_97, C_98]: (k1_xboole_0=B_96 | k1_relset_1(A_97, B_96, C_98)=A_97 | ~v1_funct_2(C_98, A_97, B_96) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.03/1.76  tff(c_284, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_277])).
% 4.03/1.76  tff(c_291, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_212, c_284])).
% 4.03/1.76  tff(c_292, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_61, c_291])).
% 4.03/1.76  tff(c_419, plain, (![A_111, B_112]: (r2_hidden('#skF_1'(A_111, B_112), k1_relat_1(A_111)) | r1_partfun1(A_111, B_112) | ~r1_tarski(k1_relat_1(A_111), k1_relat_1(B_112)) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.03/1.76  tff(c_213, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_200])).
% 4.03/1.76  tff(c_60, plain, (![E_36]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.03/1.76  tff(c_108, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_72, c_60])).
% 4.03/1.76  tff(c_218, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_108])).
% 4.03/1.76  tff(c_423, plain, (![B_112]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_112))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_112)) | r1_partfun1('#skF_4', B_112) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_112)) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_419, c_218])).
% 4.03/1.76  tff(c_440, plain, (![B_116]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_116))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_116)) | r1_partfun1('#skF_4', B_116) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_116)) | ~v1_funct_1(B_116) | ~v1_relat_1(B_116))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_48, c_423])).
% 4.03/1.76  tff(c_443, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_292, c_440])).
% 4.03/1.76  tff(c_448, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_44, c_443])).
% 4.03/1.76  tff(c_449, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_448])).
% 4.03/1.76  tff(c_533, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_449])).
% 4.03/1.76  tff(c_536, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_533])).
% 4.03/1.76  tff(c_540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_124, c_536])).
% 4.03/1.76  tff(c_542, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_449])).
% 4.03/1.76  tff(c_541, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_449])).
% 4.03/1.76  tff(c_596, plain, (![B_134, A_135]: (k1_funct_1(B_134, '#skF_1'(A_135, B_134))!=k1_funct_1(A_135, '#skF_1'(A_135, B_134)) | r1_partfun1(A_135, B_134) | ~r1_tarski(k1_relat_1(A_135), k1_relat_1(B_134)) | ~v1_funct_1(B_134) | ~v1_relat_1(B_134) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.03/1.76  tff(c_598, plain, (r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_541, c_596])).
% 4.03/1.76  tff(c_601, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_48, c_91, c_44, c_542, c_292, c_598])).
% 4.03/1.76  tff(c_603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_601])).
% 4.03/1.76  tff(c_604, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 4.03/1.76  tff(c_619, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_613])).
% 4.03/1.76  tff(c_626, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_619])).
% 4.03/1.76  tff(c_605, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 4.03/1.76  tff(c_698, plain, (![A_155, B_156, C_157]: (k1_relset_1(A_155, B_156, C_157)=k1_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.03/1.76  tff(c_710, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_698])).
% 4.03/1.76  tff(c_849, plain, (![B_195, A_196, C_197]: (k1_xboole_0=B_195 | k1_relset_1(A_196, B_195, C_197)=A_196 | ~v1_funct_2(C_197, A_196, B_195) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_196, B_195))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.03/1.76  tff(c_856, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_849])).
% 4.03/1.76  tff(c_863, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_710, c_856])).
% 4.03/1.76  tff(c_864, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_61, c_863])).
% 4.03/1.76  tff(c_711, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_698])).
% 4.03/1.76  tff(c_52, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.03/1.76  tff(c_607, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_605, c_52])).
% 4.03/1.76  tff(c_716, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_711, c_607])).
% 4.03/1.76  tff(c_964, plain, (![B_209, C_210, A_211]: (k1_funct_1(B_209, C_210)=k1_funct_1(A_211, C_210) | ~r2_hidden(C_210, k1_relat_1(A_211)) | ~r1_partfun1(A_211, B_209) | ~r1_tarski(k1_relat_1(A_211), k1_relat_1(B_209)) | ~v1_funct_1(B_209) | ~v1_relat_1(B_209) | ~v1_funct_1(A_211) | ~v1_relat_1(A_211))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.03/1.76  tff(c_970, plain, (![B_209]: (k1_funct_1(B_209, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_209) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_209)) | ~v1_funct_1(B_209) | ~v1_relat_1(B_209) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_716, c_964])).
% 4.03/1.76  tff(c_996, plain, (![B_212]: (k1_funct_1(B_212, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_212) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_212)) | ~v1_funct_1(B_212) | ~v1_relat_1(B_212))), inference(demodulation, [status(thm), theory('equality')], [c_629, c_48, c_970])).
% 4.03/1.76  tff(c_999, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_864, c_996])).
% 4.03/1.76  tff(c_1004, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_626, c_44, c_605, c_999])).
% 4.03/1.76  tff(c_1005, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_604, c_1004])).
% 4.03/1.76  tff(c_1011, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_1005])).
% 4.03/1.76  tff(c_1015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_629, c_697, c_1011])).
% 4.03/1.76  tff(c_1017, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 4.03/1.76  tff(c_1016, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_38])).
% 4.03/1.76  tff(c_1022, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1017, c_1016])).
% 4.03/1.76  tff(c_1033, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_46])).
% 4.03/1.76  tff(c_1637, plain, (![B_319, A_320]: (v1_relat_1(B_319) | ~m1_subset_1(B_319, k1_zfmisc_1(A_320)) | ~v1_relat_1(A_320))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.03/1.76  tff(c_1646, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_1033, c_1637])).
% 4.03/1.76  tff(c_1653, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1646])).
% 4.03/1.76  tff(c_1708, plain, (![C_333, A_334, B_335]: (v4_relat_1(C_333, A_334) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.03/1.76  tff(c_1721, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1033, c_1708])).
% 4.03/1.76  tff(c_1044, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_50])).
% 4.03/1.76  tff(c_1050, plain, (![B_219, A_220]: (v1_relat_1(B_219) | ~m1_subset_1(B_219, k1_zfmisc_1(A_220)) | ~v1_relat_1(A_220))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.03/1.76  tff(c_1059, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_1033, c_1050])).
% 4.03/1.76  tff(c_1066, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1059])).
% 4.03/1.76  tff(c_1034, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_40])).
% 4.03/1.76  tff(c_1056, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_1034, c_1050])).
% 4.03/1.76  tff(c_1063, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1056])).
% 4.03/1.76  tff(c_1085, plain, (![C_226, A_227, B_228]: (v4_relat_1(C_226, A_227) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.03/1.76  tff(c_1098, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1033, c_1085])).
% 4.03/1.76  tff(c_1027, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_42])).
% 4.03/1.76  tff(c_1177, plain, (![A_250, B_251, C_252]: (k1_relset_1(A_250, B_251, C_252)=k1_relat_1(C_252) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.03/1.76  tff(c_1189, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1034, c_1177])).
% 4.03/1.76  tff(c_28, plain, (![B_17, C_18]: (k1_relset_1(k1_xboole_0, B_17, C_18)=k1_xboole_0 | ~v1_funct_2(C_18, k1_xboole_0, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.03/1.76  tff(c_1289, plain, (![B_265, C_266]: (k1_relset_1('#skF_3', B_265, C_266)='#skF_3' | ~v1_funct_2(C_266, '#skF_3', B_265) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_265))))), inference(demodulation, [status(thm), theory('equality')], [c_1017, c_1017, c_1017, c_1017, c_28])).
% 4.03/1.76  tff(c_1296, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1034, c_1289])).
% 4.03/1.76  tff(c_1303, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1027, c_1189, c_1296])).
% 4.03/1.76  tff(c_1468, plain, (![A_287, B_288]: (r2_hidden('#skF_1'(A_287, B_288), k1_relat_1(A_287)) | r1_partfun1(A_287, B_288) | ~r1_tarski(k1_relat_1(A_287), k1_relat_1(B_288)) | ~v1_funct_1(B_288) | ~v1_relat_1(B_288) | ~v1_funct_1(A_287) | ~v1_relat_1(A_287))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.03/1.76  tff(c_1190, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1033, c_1177])).
% 4.03/1.76  tff(c_1081, plain, (![E_36]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relset_1('#skF_3', '#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_60])).
% 4.03/1.76  tff(c_1082, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relset_1('#skF_3', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1044, c_1081])).
% 4.03/1.76  tff(c_1195, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1190, c_1082])).
% 4.03/1.76  tff(c_1472, plain, (![B_288]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_288))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_288)) | r1_partfun1('#skF_4', B_288) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_288)) | ~v1_funct_1(B_288) | ~v1_relat_1(B_288) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1468, c_1195])).
% 4.03/1.76  tff(c_1573, plain, (![B_313]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_313))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_313)) | r1_partfun1('#skF_4', B_313) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_313)) | ~v1_funct_1(B_313) | ~v1_relat_1(B_313))), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_48, c_1472])).
% 4.03/1.76  tff(c_1576, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1303, c_1573])).
% 4.03/1.76  tff(c_1581, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_44, c_1576])).
% 4.03/1.76  tff(c_1582, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1044, c_1581])).
% 4.03/1.76  tff(c_1586, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1582])).
% 4.03/1.76  tff(c_1589, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_1586])).
% 4.03/1.76  tff(c_1593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1066, c_1098, c_1589])).
% 4.03/1.76  tff(c_1595, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_1582])).
% 4.03/1.76  tff(c_1594, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1582])).
% 4.03/1.76  tff(c_1620, plain, (![B_315, A_316]: (k1_funct_1(B_315, '#skF_1'(A_316, B_315))!=k1_funct_1(A_316, '#skF_1'(A_316, B_315)) | r1_partfun1(A_316, B_315) | ~r1_tarski(k1_relat_1(A_316), k1_relat_1(B_315)) | ~v1_funct_1(B_315) | ~v1_relat_1(B_315) | ~v1_funct_1(A_316) | ~v1_relat_1(A_316))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.03/1.76  tff(c_1622, plain, (r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1594, c_1620])).
% 4.03/1.76  tff(c_1625, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_48, c_1063, c_44, c_1595, c_1303, c_1622])).
% 4.03/1.76  tff(c_1627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1044, c_1625])).
% 4.03/1.76  tff(c_1628, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 4.03/1.76  tff(c_1643, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_1034, c_1637])).
% 4.03/1.76  tff(c_1650, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1643])).
% 4.03/1.76  tff(c_1629, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 4.03/1.76  tff(c_1722, plain, (![A_336, B_337, C_338]: (k1_relset_1(A_336, B_337, C_338)=k1_relat_1(C_338) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_336, B_337))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.03/1.76  tff(c_1734, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1034, c_1722])).
% 4.03/1.76  tff(c_1856, plain, (![B_361, C_362]: (k1_relset_1('#skF_3', B_361, C_362)='#skF_3' | ~v1_funct_2(C_362, '#skF_3', B_361) | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_361))))), inference(demodulation, [status(thm), theory('equality')], [c_1017, c_1017, c_1017, c_1017, c_28])).
% 4.03/1.76  tff(c_1863, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1034, c_1856])).
% 4.03/1.76  tff(c_1870, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1027, c_1734, c_1863])).
% 4.03/1.76  tff(c_1735, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1033, c_1722])).
% 4.03/1.76  tff(c_1631, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_3', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1629, c_1022, c_52])).
% 4.03/1.76  tff(c_1740, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1735, c_1631])).
% 4.03/1.76  tff(c_2139, plain, (![B_406, C_407, A_408]: (k1_funct_1(B_406, C_407)=k1_funct_1(A_408, C_407) | ~r2_hidden(C_407, k1_relat_1(A_408)) | ~r1_partfun1(A_408, B_406) | ~r1_tarski(k1_relat_1(A_408), k1_relat_1(B_406)) | ~v1_funct_1(B_406) | ~v1_relat_1(B_406) | ~v1_funct_1(A_408) | ~v1_relat_1(A_408))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.03/1.76  tff(c_2145, plain, (![B_406]: (k1_funct_1(B_406, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_406) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_406)) | ~v1_funct_1(B_406) | ~v1_relat_1(B_406) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1740, c_2139])).
% 4.03/1.76  tff(c_2152, plain, (![B_409]: (k1_funct_1(B_409, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_409) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_409)) | ~v1_funct_1(B_409) | ~v1_relat_1(B_409))), inference(demodulation, [status(thm), theory('equality')], [c_1653, c_48, c_2145])).
% 4.03/1.76  tff(c_2155, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1870, c_2152])).
% 4.03/1.76  tff(c_2160, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1650, c_44, c_1629, c_2155])).
% 4.03/1.76  tff(c_2161, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1628, c_2160])).
% 4.03/1.76  tff(c_2167, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_2161])).
% 4.03/1.76  tff(c_2171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1653, c_1721, c_2167])).
% 4.03/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.76  
% 4.03/1.76  Inference rules
% 4.03/1.76  ----------------------
% 4.03/1.76  #Ref     : 2
% 4.03/1.76  #Sup     : 385
% 4.03/1.76  #Fact    : 0
% 4.03/1.76  #Define  : 0
% 4.03/1.76  #Split   : 15
% 4.03/1.76  #Chain   : 0
% 4.03/1.76  #Close   : 0
% 4.03/1.76  
% 4.03/1.76  Ordering : KBO
% 4.03/1.76  
% 4.03/1.76  Simplification rules
% 4.03/1.76  ----------------------
% 4.03/1.76  #Subsume      : 66
% 4.03/1.76  #Demod        : 444
% 4.03/1.76  #Tautology    : 144
% 4.03/1.76  #SimpNegUnit  : 51
% 4.03/1.76  #BackRed      : 38
% 4.03/1.76  
% 4.03/1.76  #Partial instantiations: 0
% 4.03/1.76  #Strategies tried      : 1
% 4.03/1.76  
% 4.03/1.76  Timing (in seconds)
% 4.03/1.76  ----------------------
% 4.03/1.76  Preprocessing        : 0.34
% 4.03/1.76  Parsing              : 0.18
% 4.03/1.76  CNF conversion       : 0.02
% 4.03/1.76  Main loop            : 0.58
% 4.03/1.76  Inferencing          : 0.22
% 4.03/1.76  Reduction            : 0.18
% 4.03/1.76  Demodulation         : 0.12
% 4.03/1.76  BG Simplification    : 0.03
% 4.03/1.76  Subsumption          : 0.10
% 4.03/1.76  Abstraction          : 0.03
% 4.03/1.76  MUC search           : 0.00
% 4.03/1.76  Cooper               : 0.00
% 4.03/1.76  Total                : 0.99
% 4.03/1.76  Index Insertion      : 0.00
% 4.03/1.76  Index Deletion       : 0.00
% 4.03/1.76  Index Matching       : 0.00
% 4.03/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
