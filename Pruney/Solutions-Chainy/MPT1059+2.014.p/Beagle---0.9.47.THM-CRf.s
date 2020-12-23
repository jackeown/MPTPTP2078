%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:34 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 124 expanded)
%              Number of leaves         :   36 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  132 ( 305 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > o_1_1_funct_2 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_1_1_funct_2,type,(
    o_1_1_funct_2: $i > $i )).

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

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

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

tff(f_126,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
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

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_93,axiom,(
    ! [A] : m1_subset_1(o_1_1_funct_2(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_1_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    m1_subset_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_110,plain,(
    ! [C_62,B_63,A_64] :
      ( v5_relat_1(C_62,B_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_123,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_110])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_85,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_72])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_46,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_402,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_415,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_402])).

tff(c_977,plain,(
    ! [B_158,A_159,C_160] :
      ( k1_xboole_0 = B_158
      | k1_relset_1(A_159,B_158,C_160) = A_159
      | ~ v1_funct_2(C_160,A_159,B_158)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_159,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_984,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_977])).

tff(c_992,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_415,c_984])).

tff(c_994,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_992])).

tff(c_1320,plain,(
    ! [A_179,B_180,C_181] :
      ( k7_partfun1(A_179,B_180,C_181) = k1_funct_1(B_180,C_181)
      | ~ r2_hidden(C_181,k1_relat_1(B_180))
      | ~ v1_funct_1(B_180)
      | ~ v5_relat_1(B_180,A_179)
      | ~ v1_relat_1(B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1322,plain,(
    ! [A_179,C_181] :
      ( k7_partfun1(A_179,'#skF_3',C_181) = k1_funct_1('#skF_3',C_181)
      | ~ r2_hidden(C_181,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_179)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_994,c_1320])).

tff(c_1334,plain,(
    ! [A_182,C_183] :
      ( k7_partfun1(A_182,'#skF_3',C_183) = k1_funct_1('#skF_3',C_183)
      | ~ r2_hidden(C_183,'#skF_1')
      | ~ v5_relat_1('#skF_3',A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_48,c_1322])).

tff(c_1337,plain,(
    ! [A_182,A_5] :
      ( k7_partfun1(A_182,'#skF_3',A_5) = k1_funct_1('#skF_3',A_5)
      | ~ v5_relat_1('#skF_3',A_182)
      | v1_xboole_0('#skF_1')
      | ~ m1_subset_1(A_5,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6,c_1334])).

tff(c_1341,plain,(
    ! [A_184,A_185] :
      ( k7_partfun1(A_184,'#skF_3',A_185) = k1_funct_1('#skF_3',A_185)
      | ~ v5_relat_1('#skF_3',A_184)
      | ~ m1_subset_1(A_185,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1337])).

tff(c_1349,plain,(
    ! [A_186] :
      ( k7_partfun1('#skF_2','#skF_3',A_186) = k1_funct_1('#skF_3',A_186)
      | ~ m1_subset_1(A_186,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_123,c_1341])).

tff(c_1358,plain,(
    k7_partfun1('#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1349])).

tff(c_40,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') != k7_partfun1('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1359,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') != k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1358,c_40])).

tff(c_1373,plain,(
    ! [A_188,B_189,C_190,D_191] :
      ( k3_funct_2(A_188,B_189,C_190,D_191) = k1_funct_1(C_190,D_191)
      | ~ m1_subset_1(D_191,A_188)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189)))
      | ~ v1_funct_2(C_190,A_188,B_189)
      | ~ v1_funct_1(C_190)
      | v1_xboole_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1383,plain,(
    ! [B_189,C_190] :
      ( k3_funct_2('#skF_1',B_189,C_190,'#skF_4') = k1_funct_1(C_190,'#skF_4')
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_189)))
      | ~ v1_funct_2(C_190,'#skF_1',B_189)
      | ~ v1_funct_1(C_190)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_1373])).

tff(c_1458,plain,(
    ! [B_195,C_196] :
      ( k3_funct_2('#skF_1',B_195,C_196,'#skF_4') = k1_funct_1(C_196,'#skF_4')
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_195)))
      | ~ v1_funct_2(C_196,'#skF_1',B_195)
      | ~ v1_funct_1(C_196) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1383])).

tff(c_1465,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1458])).

tff(c_1473,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1465])).

tff(c_1475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1359,c_1473])).

tff(c_1476,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_992])).

tff(c_36,plain,(
    ! [A_27] : m1_subset_1(o_1_1_funct_2(A_27),A_27) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    ! [A_55,B_56] :
      ( r2_hidden(A_55,B_56)
      | v1_xboole_0(B_56)
      | ~ m1_subset_1(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_126,plain,(
    ! [B_67,A_68] :
      ( ~ r1_tarski(B_67,A_68)
      | v1_xboole_0(B_67)
      | ~ m1_subset_1(A_68,B_67) ) ),
    inference(resolution,[status(thm)],[c_87,c_12])).

tff(c_138,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_126])).

tff(c_150,plain,(
    ! [A_72] : ~ m1_subset_1(A_72,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_155,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_36,c_150])).

tff(c_156,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_1505,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1476,c_156])).

tff(c_1509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:30:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.64  
% 3.64/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.64  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > o_1_1_funct_2 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.64/1.64  
% 3.64/1.64  %Foreground sorts:
% 3.64/1.64  
% 3.64/1.64  
% 3.64/1.64  %Background operators:
% 3.64/1.64  
% 3.64/1.64  
% 3.64/1.64  %Foreground operators:
% 3.64/1.64  tff(o_1_1_funct_2, type, o_1_1_funct_2: $i > $i).
% 3.64/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.64/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.64/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.64/1.64  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.64/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.64/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.64/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.64/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.64/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.64/1.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.64/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.64/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.64/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.64/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.64/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.64/1.64  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.64/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.64/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.64/1.64  
% 3.99/1.67  tff(f_126, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 3.99/1.67  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.99/1.67  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.99/1.67  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.99/1.67  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.99/1.67  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.99/1.67  tff(f_91, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 3.99/1.67  tff(f_106, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.99/1.67  tff(f_93, axiom, (![A]: m1_subset_1(o_1_1_funct_2(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_1_1_funct_2)).
% 3.99/1.67  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.99/1.67  tff(f_48, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.99/1.67  tff(c_50, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.99/1.67  tff(c_42, plain, (m1_subset_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.99/1.67  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.99/1.67  tff(c_110, plain, (![C_62, B_63, A_64]: (v5_relat_1(C_62, B_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.99/1.67  tff(c_123, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_110])).
% 3.99/1.67  tff(c_52, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.99/1.67  tff(c_6, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.99/1.67  tff(c_72, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.99/1.67  tff(c_85, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_72])).
% 3.99/1.67  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.99/1.67  tff(c_46, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.99/1.67  tff(c_402, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.99/1.67  tff(c_415, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_402])).
% 3.99/1.67  tff(c_977, plain, (![B_158, A_159, C_160]: (k1_xboole_0=B_158 | k1_relset_1(A_159, B_158, C_160)=A_159 | ~v1_funct_2(C_160, A_159, B_158) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_159, B_158))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.99/1.67  tff(c_984, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_977])).
% 3.99/1.67  tff(c_992, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_415, c_984])).
% 3.99/1.67  tff(c_994, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_992])).
% 3.99/1.67  tff(c_1320, plain, (![A_179, B_180, C_181]: (k7_partfun1(A_179, B_180, C_181)=k1_funct_1(B_180, C_181) | ~r2_hidden(C_181, k1_relat_1(B_180)) | ~v1_funct_1(B_180) | ~v5_relat_1(B_180, A_179) | ~v1_relat_1(B_180))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.99/1.67  tff(c_1322, plain, (![A_179, C_181]: (k7_partfun1(A_179, '#skF_3', C_181)=k1_funct_1('#skF_3', C_181) | ~r2_hidden(C_181, '#skF_1') | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', A_179) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_994, c_1320])).
% 3.99/1.67  tff(c_1334, plain, (![A_182, C_183]: (k7_partfun1(A_182, '#skF_3', C_183)=k1_funct_1('#skF_3', C_183) | ~r2_hidden(C_183, '#skF_1') | ~v5_relat_1('#skF_3', A_182))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_48, c_1322])).
% 3.99/1.67  tff(c_1337, plain, (![A_182, A_5]: (k7_partfun1(A_182, '#skF_3', A_5)=k1_funct_1('#skF_3', A_5) | ~v5_relat_1('#skF_3', A_182) | v1_xboole_0('#skF_1') | ~m1_subset_1(A_5, '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1334])).
% 3.99/1.67  tff(c_1341, plain, (![A_184, A_185]: (k7_partfun1(A_184, '#skF_3', A_185)=k1_funct_1('#skF_3', A_185) | ~v5_relat_1('#skF_3', A_184) | ~m1_subset_1(A_185, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_52, c_1337])).
% 3.99/1.67  tff(c_1349, plain, (![A_186]: (k7_partfun1('#skF_2', '#skF_3', A_186)=k1_funct_1('#skF_3', A_186) | ~m1_subset_1(A_186, '#skF_1'))), inference(resolution, [status(thm)], [c_123, c_1341])).
% 3.99/1.67  tff(c_1358, plain, (k7_partfun1('#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_1349])).
% 3.99/1.67  tff(c_40, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k7_partfun1('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.99/1.67  tff(c_1359, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_funct_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1358, c_40])).
% 3.99/1.67  tff(c_1373, plain, (![A_188, B_189, C_190, D_191]: (k3_funct_2(A_188, B_189, C_190, D_191)=k1_funct_1(C_190, D_191) | ~m1_subset_1(D_191, A_188) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))) | ~v1_funct_2(C_190, A_188, B_189) | ~v1_funct_1(C_190) | v1_xboole_0(A_188))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.99/1.67  tff(c_1383, plain, (![B_189, C_190]: (k3_funct_2('#skF_1', B_189, C_190, '#skF_4')=k1_funct_1(C_190, '#skF_4') | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_189))) | ~v1_funct_2(C_190, '#skF_1', B_189) | ~v1_funct_1(C_190) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_1373])).
% 3.99/1.67  tff(c_1458, plain, (![B_195, C_196]: (k3_funct_2('#skF_1', B_195, C_196, '#skF_4')=k1_funct_1(C_196, '#skF_4') | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_195))) | ~v1_funct_2(C_196, '#skF_1', B_195) | ~v1_funct_1(C_196))), inference(negUnitSimplification, [status(thm)], [c_52, c_1383])).
% 3.99/1.67  tff(c_1465, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1458])).
% 3.99/1.67  tff(c_1473, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1465])).
% 3.99/1.67  tff(c_1475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1359, c_1473])).
% 3.99/1.67  tff(c_1476, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_992])).
% 3.99/1.67  tff(c_36, plain, (![A_27]: (m1_subset_1(o_1_1_funct_2(A_27), A_27))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.99/1.67  tff(c_4, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.99/1.67  tff(c_87, plain, (![A_55, B_56]: (r2_hidden(A_55, B_56) | v1_xboole_0(B_56) | ~m1_subset_1(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.99/1.67  tff(c_12, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.99/1.67  tff(c_126, plain, (![B_67, A_68]: (~r1_tarski(B_67, A_68) | v1_xboole_0(B_67) | ~m1_subset_1(A_68, B_67))), inference(resolution, [status(thm)], [c_87, c_12])).
% 3.99/1.67  tff(c_138, plain, (![A_4]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_126])).
% 3.99/1.67  tff(c_150, plain, (![A_72]: (~m1_subset_1(A_72, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_138])).
% 3.99/1.67  tff(c_155, plain, $false, inference(resolution, [status(thm)], [c_36, c_150])).
% 3.99/1.67  tff(c_156, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_138])).
% 3.99/1.67  tff(c_1505, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1476, c_156])).
% 3.99/1.67  tff(c_1509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1505])).
% 3.99/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.67  
% 3.99/1.67  Inference rules
% 3.99/1.67  ----------------------
% 3.99/1.67  #Ref     : 0
% 3.99/1.67  #Sup     : 285
% 3.99/1.67  #Fact    : 0
% 3.99/1.67  #Define  : 0
% 3.99/1.67  #Split   : 5
% 3.99/1.67  #Chain   : 0
% 3.99/1.67  #Close   : 0
% 3.99/1.67  
% 3.99/1.67  Ordering : KBO
% 3.99/1.67  
% 3.99/1.67  Simplification rules
% 3.99/1.67  ----------------------
% 3.99/1.67  #Subsume      : 13
% 3.99/1.67  #Demod        : 231
% 3.99/1.67  #Tautology    : 129
% 3.99/1.67  #SimpNegUnit  : 4
% 3.99/1.67  #BackRed      : 53
% 3.99/1.67  
% 3.99/1.67  #Partial instantiations: 0
% 3.99/1.67  #Strategies tried      : 1
% 3.99/1.67  
% 3.99/1.67  Timing (in seconds)
% 3.99/1.67  ----------------------
% 3.99/1.68  Preprocessing        : 0.34
% 3.99/1.68  Parsing              : 0.18
% 3.99/1.68  CNF conversion       : 0.02
% 3.99/1.68  Main loop            : 0.55
% 3.99/1.68  Inferencing          : 0.19
% 3.99/1.68  Reduction            : 0.19
% 3.99/1.68  Demodulation         : 0.14
% 3.99/1.68  BG Simplification    : 0.03
% 3.99/1.68  Subsumption          : 0.09
% 3.99/1.68  Abstraction          : 0.02
% 3.99/1.68  MUC search           : 0.00
% 3.99/1.68  Cooper               : 0.00
% 3.99/1.68  Total                : 0.94
% 3.99/1.68  Index Insertion      : 0.00
% 3.99/1.68  Index Deletion       : 0.00
% 3.99/1.68  Index Matching       : 0.00
% 3.99/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
