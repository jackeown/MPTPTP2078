%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:35 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 114 expanded)
%              Number of leaves         :   37 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  132 ( 285 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_105,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_40,plain,(
    m1_subset_1('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_97,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_101,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_97])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_79,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_82,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_85,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_82])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_102,plain,(
    ! [A_64,B_65,C_66] :
      ( k1_relset_1(A_64,B_65,C_66) = k1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_106,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_102])).

tff(c_121,plain,(
    ! [B_77,A_78,C_79] :
      ( k1_xboole_0 = B_77
      | k1_relset_1(A_78,B_77,C_79) = A_78
      | ~ v1_funct_2(C_79,A_78,B_77)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_124,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_121])).

tff(c_127,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_106,c_124])).

tff(c_128,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_138,plain,(
    ! [A_80,B_81,C_82] :
      ( k7_partfun1(A_80,B_81,C_82) = k1_funct_1(B_81,C_82)
      | ~ r2_hidden(C_82,k1_relat_1(B_81))
      | ~ v1_funct_1(B_81)
      | ~ v5_relat_1(B_81,A_80)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_140,plain,(
    ! [A_80,C_82] :
      ( k7_partfun1(A_80,'#skF_4',C_82) = k1_funct_1('#skF_4',C_82)
      | ~ r2_hidden(C_82,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_80)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_138])).

tff(c_151,plain,(
    ! [A_83,C_84] :
      ( k7_partfun1(A_83,'#skF_4',C_84) = k1_funct_1('#skF_4',C_84)
      | ~ r2_hidden(C_84,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_46,c_140])).

tff(c_154,plain,(
    ! [A_83,A_6] :
      ( k7_partfun1(A_83,'#skF_4',A_6) = k1_funct_1('#skF_4',A_6)
      | ~ v5_relat_1('#skF_4',A_83)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_6,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_151])).

tff(c_182,plain,(
    ! [A_90,A_91] :
      ( k7_partfun1(A_90,'#skF_4',A_91) = k1_funct_1('#skF_4',A_91)
      | ~ v5_relat_1('#skF_4',A_90)
      | ~ m1_subset_1(A_91,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_154])).

tff(c_186,plain,(
    ! [A_92] :
      ( k7_partfun1('#skF_3','#skF_4',A_92) = k1_funct_1('#skF_4',A_92)
      | ~ m1_subset_1(A_92,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_101,c_182])).

tff(c_190,plain,(
    k7_partfun1('#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_186])).

tff(c_38,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k7_partfun1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_191,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_38])).

tff(c_164,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k3_funct_2(A_85,B_86,C_87,D_88) = k1_funct_1(C_87,D_88)
      | ~ m1_subset_1(D_88,A_85)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_2(C_87,A_85,B_86)
      | ~ v1_funct_1(C_87)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_168,plain,(
    ! [B_86,C_87] :
      ( k3_funct_2('#skF_2',B_86,C_87,'#skF_5') = k1_funct_1(C_87,'#skF_5')
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_86)))
      | ~ v1_funct_2(C_87,'#skF_2',B_86)
      | ~ v1_funct_1(C_87)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_164])).

tff(c_196,plain,(
    ! [B_93,C_94] :
      ( k3_funct_2('#skF_2',B_93,C_94,'#skF_5') = k1_funct_1(C_94,'#skF_5')
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_93)))
      | ~ v1_funct_2(C_94,'#skF_2',B_93)
      | ~ v1_funct_1(C_94) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_168])).

tff(c_199,plain,
    ( k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_196])).

tff(c_202,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_199])).

tff(c_204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_202])).

tff(c_205,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    ! [A_50] :
      ( v1_xboole_0(A_50)
      | r2_hidden('#skF_1'(A_50),A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,(
    ! [A_51] :
      ( ~ r1_tarski(A_51,'#skF_1'(A_51))
      | v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_55,c_14])).

tff(c_69,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_213,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_69])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:12:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.31  
% 2.17/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.31  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.17/1.31  
% 2.17/1.31  %Foreground sorts:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Background operators:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Foreground operators:
% 2.17/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.17/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.31  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.17/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.17/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.17/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.17/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.17/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.31  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.17/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.31  
% 2.44/1.32  tff(f_125, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 2.44/1.32  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.44/1.32  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.44/1.32  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.44/1.32  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.44/1.32  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.44/1.32  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.44/1.32  tff(f_92, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 2.44/1.32  tff(f_105, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.44/1.32  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.44/1.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.44/1.32  tff(f_53, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.44/1.32  tff(c_48, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.44/1.32  tff(c_40, plain, (m1_subset_1('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.44/1.32  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.44/1.32  tff(c_97, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.44/1.32  tff(c_101, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_97])).
% 2.44/1.32  tff(c_50, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.44/1.32  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.44/1.32  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.44/1.32  tff(c_79, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.44/1.32  tff(c_82, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_79])).
% 2.44/1.32  tff(c_85, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_82])).
% 2.44/1.32  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.44/1.32  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.44/1.32  tff(c_102, plain, (![A_64, B_65, C_66]: (k1_relset_1(A_64, B_65, C_66)=k1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.44/1.32  tff(c_106, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_102])).
% 2.44/1.32  tff(c_121, plain, (![B_77, A_78, C_79]: (k1_xboole_0=B_77 | k1_relset_1(A_78, B_77, C_79)=A_78 | ~v1_funct_2(C_79, A_78, B_77) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.44/1.32  tff(c_124, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_121])).
% 2.44/1.32  tff(c_127, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_106, c_124])).
% 2.44/1.32  tff(c_128, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_127])).
% 2.44/1.32  tff(c_138, plain, (![A_80, B_81, C_82]: (k7_partfun1(A_80, B_81, C_82)=k1_funct_1(B_81, C_82) | ~r2_hidden(C_82, k1_relat_1(B_81)) | ~v1_funct_1(B_81) | ~v5_relat_1(B_81, A_80) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.44/1.32  tff(c_140, plain, (![A_80, C_82]: (k7_partfun1(A_80, '#skF_4', C_82)=k1_funct_1('#skF_4', C_82) | ~r2_hidden(C_82, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_80) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_138])).
% 2.44/1.32  tff(c_151, plain, (![A_83, C_84]: (k7_partfun1(A_83, '#skF_4', C_84)=k1_funct_1('#skF_4', C_84) | ~r2_hidden(C_84, '#skF_2') | ~v5_relat_1('#skF_4', A_83))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_46, c_140])).
% 2.44/1.32  tff(c_154, plain, (![A_83, A_6]: (k7_partfun1(A_83, '#skF_4', A_6)=k1_funct_1('#skF_4', A_6) | ~v5_relat_1('#skF_4', A_83) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_6, '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_151])).
% 2.44/1.32  tff(c_182, plain, (![A_90, A_91]: (k7_partfun1(A_90, '#skF_4', A_91)=k1_funct_1('#skF_4', A_91) | ~v5_relat_1('#skF_4', A_90) | ~m1_subset_1(A_91, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_154])).
% 2.44/1.32  tff(c_186, plain, (![A_92]: (k7_partfun1('#skF_3', '#skF_4', A_92)=k1_funct_1('#skF_4', A_92) | ~m1_subset_1(A_92, '#skF_2'))), inference(resolution, [status(thm)], [c_101, c_182])).
% 2.44/1.32  tff(c_190, plain, (k7_partfun1('#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_186])).
% 2.44/1.32  tff(c_38, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k7_partfun1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.44/1.32  tff(c_191, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_38])).
% 2.44/1.32  tff(c_164, plain, (![A_85, B_86, C_87, D_88]: (k3_funct_2(A_85, B_86, C_87, D_88)=k1_funct_1(C_87, D_88) | ~m1_subset_1(D_88, A_85) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_2(C_87, A_85, B_86) | ~v1_funct_1(C_87) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.44/1.33  tff(c_168, plain, (![B_86, C_87]: (k3_funct_2('#skF_2', B_86, C_87, '#skF_5')=k1_funct_1(C_87, '#skF_5') | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_86))) | ~v1_funct_2(C_87, '#skF_2', B_86) | ~v1_funct_1(C_87) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_164])).
% 2.44/1.33  tff(c_196, plain, (![B_93, C_94]: (k3_funct_2('#skF_2', B_93, C_94, '#skF_5')=k1_funct_1(C_94, '#skF_5') | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_93))) | ~v1_funct_2(C_94, '#skF_2', B_93) | ~v1_funct_1(C_94))), inference(negUnitSimplification, [status(thm)], [c_50, c_168])).
% 2.44/1.33  tff(c_199, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_196])).
% 2.44/1.33  tff(c_202, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_199])).
% 2.44/1.33  tff(c_204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_202])).
% 2.44/1.33  tff(c_205, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_127])).
% 2.44/1.33  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.44/1.33  tff(c_55, plain, (![A_50]: (v1_xboole_0(A_50) | r2_hidden('#skF_1'(A_50), A_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.33  tff(c_14, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.44/1.33  tff(c_64, plain, (![A_51]: (~r1_tarski(A_51, '#skF_1'(A_51)) | v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_55, c_14])).
% 2.44/1.33  tff(c_69, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_64])).
% 2.44/1.33  tff(c_213, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_69])).
% 2.44/1.33  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_213])).
% 2.44/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.33  
% 2.44/1.33  Inference rules
% 2.44/1.33  ----------------------
% 2.44/1.33  #Ref     : 0
% 2.44/1.33  #Sup     : 32
% 2.44/1.33  #Fact    : 0
% 2.44/1.33  #Define  : 0
% 2.44/1.33  #Split   : 1
% 2.44/1.33  #Chain   : 0
% 2.44/1.33  #Close   : 0
% 2.44/1.33  
% 2.44/1.33  Ordering : KBO
% 2.44/1.33  
% 2.44/1.33  Simplification rules
% 2.44/1.33  ----------------------
% 2.44/1.33  #Subsume      : 0
% 2.44/1.33  #Demod        : 33
% 2.44/1.33  #Tautology    : 14
% 2.44/1.33  #SimpNegUnit  : 5
% 2.44/1.33  #BackRed      : 10
% 2.44/1.33  
% 2.44/1.33  #Partial instantiations: 0
% 2.44/1.33  #Strategies tried      : 1
% 2.44/1.33  
% 2.44/1.33  Timing (in seconds)
% 2.44/1.33  ----------------------
% 2.44/1.33  Preprocessing        : 0.35
% 2.44/1.33  Parsing              : 0.19
% 2.44/1.33  CNF conversion       : 0.02
% 2.44/1.33  Main loop            : 0.19
% 2.44/1.33  Inferencing          : 0.07
% 2.44/1.33  Reduction            : 0.06
% 2.44/1.33  Demodulation         : 0.04
% 2.44/1.33  BG Simplification    : 0.01
% 2.44/1.33  Subsumption          : 0.03
% 2.44/1.33  Abstraction          : 0.01
% 2.44/1.33  MUC search           : 0.00
% 2.44/1.33  Cooper               : 0.00
% 2.44/1.33  Total                : 0.57
% 2.44/1.33  Index Insertion      : 0.00
% 2.44/1.33  Index Deletion       : 0.00
% 2.44/1.33  Index Matching       : 0.00
% 2.44/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
