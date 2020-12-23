%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:35 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 130 expanded)
%              Number of leaves         :   37 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  137 ( 315 expanded)
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

tff(f_132,negated_conjecture,(
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

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_64,axiom,(
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

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_86,axiom,(
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

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_99,axiom,(
    ! [A] : m1_subset_1(o_1_1_funct_2(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_1_1_funct_2)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    m1_subset_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1225,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( k3_funct_2(A_194,B_195,C_196,D_197) = k1_funct_1(C_196,D_197)
      | ~ m1_subset_1(D_197,A_194)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195)))
      | ~ v1_funct_2(C_196,A_194,B_195)
      | ~ v1_funct_1(C_196)
      | v1_xboole_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1239,plain,(
    ! [B_195,C_196] :
      ( k3_funct_2('#skF_1',B_195,C_196,'#skF_4') = k1_funct_1(C_196,'#skF_4')
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_195)))
      | ~ v1_funct_2(C_196,'#skF_1',B_195)
      | ~ v1_funct_1(C_196)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_1225])).

tff(c_1381,plain,(
    ! [B_200,C_201] :
      ( k3_funct_2('#skF_1',B_200,C_201,'#skF_4') = k1_funct_1(C_201,'#skF_4')
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_200)))
      | ~ v1_funct_2(C_201,'#skF_1',B_200)
      | ~ v1_funct_1(C_201) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1239])).

tff(c_1392,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1381])).

tff(c_1405,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1392])).

tff(c_42,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') != k7_partfun1('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1408,plain,(
    k7_partfun1('#skF_2','#skF_3','#skF_4') != k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1405,c_42])).

tff(c_208,plain,(
    ! [C_84,B_85,A_86] :
      ( v5_relat_1(C_84,B_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_225,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_208])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_98,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_81])).

tff(c_400,plain,(
    ! [A_111,B_112,C_113] :
      ( k1_relset_1(A_111,B_112,C_113) = k1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_417,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_400])).

tff(c_1133,plain,(
    ! [B_177,A_178,C_179] :
      ( k1_xboole_0 = B_177
      | k1_relset_1(A_178,B_177,C_179) = A_178
      | ~ v1_funct_2(C_179,A_178,B_177)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_178,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1140,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_1133])).

tff(c_1152,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_417,c_1140])).

tff(c_1156,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1152])).

tff(c_1203,plain,(
    ! [A_185,B_186,C_187] :
      ( k7_partfun1(A_185,B_186,C_187) = k1_funct_1(B_186,C_187)
      | ~ r2_hidden(C_187,k1_relat_1(B_186))
      | ~ v1_funct_1(B_186)
      | ~ v5_relat_1(B_186,A_185)
      | ~ v1_relat_1(B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1205,plain,(
    ! [A_185,C_187] :
      ( k7_partfun1(A_185,'#skF_3',C_187) = k1_funct_1('#skF_3',C_187)
      | ~ r2_hidden(C_187,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_185)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1156,c_1203])).

tff(c_1711,plain,(
    ! [A_214,C_215] :
      ( k7_partfun1(A_214,'#skF_3',C_215) = k1_funct_1('#skF_3',C_215)
      | ~ r2_hidden(C_215,'#skF_1')
      | ~ v5_relat_1('#skF_3',A_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_50,c_1205])).

tff(c_1714,plain,(
    ! [A_214,A_5] :
      ( k7_partfun1(A_214,'#skF_3',A_5) = k1_funct_1('#skF_3',A_5)
      | ~ v5_relat_1('#skF_3',A_214)
      | v1_xboole_0('#skF_1')
      | ~ m1_subset_1(A_5,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6,c_1711])).

tff(c_1718,plain,(
    ! [A_216,A_217] :
      ( k7_partfun1(A_216,'#skF_3',A_217) = k1_funct_1('#skF_3',A_217)
      | ~ v5_relat_1('#skF_3',A_216)
      | ~ m1_subset_1(A_217,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1714])).

tff(c_1735,plain,(
    ! [A_220] :
      ( k7_partfun1('#skF_2','#skF_3',A_220) = k1_funct_1('#skF_3',A_220)
      | ~ m1_subset_1(A_220,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_225,c_1718])).

tff(c_1746,plain,(
    k7_partfun1('#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1735])).

tff(c_1752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1408,c_1746])).

tff(c_1753,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1152])).

tff(c_38,plain,(
    ! [A_30] : m1_subset_1(o_1_1_funct_2(A_30),A_30) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(resolution,[status(thm)],[c_4,c_62])).

tff(c_102,plain,(
    ! [A_60,B_61] :
      ( r2_hidden(A_60,B_61)
      | v1_xboole_0(B_61)
      | ~ m1_subset_1(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_126,plain,(
    ! [B_67,A_68] :
      ( ~ r1_tarski(B_67,A_68)
      | v1_xboole_0(B_67)
      | ~ m1_subset_1(A_68,B_67) ) ),
    inference(resolution,[status(thm)],[c_102,c_14])).

tff(c_138,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_78,c_126])).

tff(c_140,plain,(
    ! [A_69] : ~ m1_subset_1(A_69,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_145,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_38,c_140])).

tff(c_146,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_1786,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1753,c_146])).

tff(c_1792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1786])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.77  
% 4.13/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.78  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > o_1_1_funct_2 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.13/1.78  
% 4.13/1.78  %Foreground sorts:
% 4.13/1.78  
% 4.13/1.78  
% 4.13/1.78  %Background operators:
% 4.13/1.78  
% 4.13/1.78  
% 4.13/1.78  %Foreground operators:
% 4.13/1.78  tff(o_1_1_funct_2, type, o_1_1_funct_2: $i > $i).
% 4.13/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.13/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.13/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.78  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.13/1.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.13/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.13/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.13/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.13/1.78  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.13/1.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.13/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.13/1.78  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.13/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.13/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.13/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.13/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.13/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.13/1.78  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.13/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.13/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.13/1.78  
% 4.13/1.79  tff(f_132, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 4.13/1.79  tff(f_112, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.13/1.79  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.13/1.79  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.13/1.79  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.13/1.79  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.13/1.79  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.13/1.79  tff(f_97, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 4.13/1.79  tff(f_99, axiom, (![A]: m1_subset_1(o_1_1_funct_2(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_1_1_funct_2)).
% 4.13/1.79  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.13/1.79  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.13/1.79  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.13/1.79  tff(c_52, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.13/1.79  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.13/1.79  tff(c_48, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.13/1.79  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.13/1.79  tff(c_54, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.13/1.79  tff(c_44, plain, (m1_subset_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.13/1.79  tff(c_1225, plain, (![A_194, B_195, C_196, D_197]: (k3_funct_2(A_194, B_195, C_196, D_197)=k1_funct_1(C_196, D_197) | ~m1_subset_1(D_197, A_194) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))) | ~v1_funct_2(C_196, A_194, B_195) | ~v1_funct_1(C_196) | v1_xboole_0(A_194))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.13/1.79  tff(c_1239, plain, (![B_195, C_196]: (k3_funct_2('#skF_1', B_195, C_196, '#skF_4')=k1_funct_1(C_196, '#skF_4') | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_195))) | ~v1_funct_2(C_196, '#skF_1', B_195) | ~v1_funct_1(C_196) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_1225])).
% 4.13/1.79  tff(c_1381, plain, (![B_200, C_201]: (k3_funct_2('#skF_1', B_200, C_201, '#skF_4')=k1_funct_1(C_201, '#skF_4') | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_200))) | ~v1_funct_2(C_201, '#skF_1', B_200) | ~v1_funct_1(C_201))), inference(negUnitSimplification, [status(thm)], [c_54, c_1239])).
% 4.13/1.79  tff(c_1392, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1381])).
% 4.13/1.79  tff(c_1405, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1392])).
% 4.13/1.79  tff(c_42, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k7_partfun1('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.13/1.79  tff(c_1408, plain, (k7_partfun1('#skF_2', '#skF_3', '#skF_4')!=k1_funct_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1405, c_42])).
% 4.13/1.79  tff(c_208, plain, (![C_84, B_85, A_86]: (v5_relat_1(C_84, B_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.13/1.79  tff(c_225, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_208])).
% 4.13/1.79  tff(c_6, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.13/1.79  tff(c_81, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.13/1.79  tff(c_98, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_81])).
% 4.13/1.79  tff(c_400, plain, (![A_111, B_112, C_113]: (k1_relset_1(A_111, B_112, C_113)=k1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.13/1.79  tff(c_417, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_400])).
% 4.13/1.79  tff(c_1133, plain, (![B_177, A_178, C_179]: (k1_xboole_0=B_177 | k1_relset_1(A_178, B_177, C_179)=A_178 | ~v1_funct_2(C_179, A_178, B_177) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_178, B_177))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.13/1.79  tff(c_1140, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_1133])).
% 4.13/1.79  tff(c_1152, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_417, c_1140])).
% 4.13/1.79  tff(c_1156, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1152])).
% 4.13/1.79  tff(c_1203, plain, (![A_185, B_186, C_187]: (k7_partfun1(A_185, B_186, C_187)=k1_funct_1(B_186, C_187) | ~r2_hidden(C_187, k1_relat_1(B_186)) | ~v1_funct_1(B_186) | ~v5_relat_1(B_186, A_185) | ~v1_relat_1(B_186))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.13/1.79  tff(c_1205, plain, (![A_185, C_187]: (k7_partfun1(A_185, '#skF_3', C_187)=k1_funct_1('#skF_3', C_187) | ~r2_hidden(C_187, '#skF_1') | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', A_185) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1156, c_1203])).
% 4.13/1.79  tff(c_1711, plain, (![A_214, C_215]: (k7_partfun1(A_214, '#skF_3', C_215)=k1_funct_1('#skF_3', C_215) | ~r2_hidden(C_215, '#skF_1') | ~v5_relat_1('#skF_3', A_214))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_50, c_1205])).
% 4.13/1.79  tff(c_1714, plain, (![A_214, A_5]: (k7_partfun1(A_214, '#skF_3', A_5)=k1_funct_1('#skF_3', A_5) | ~v5_relat_1('#skF_3', A_214) | v1_xboole_0('#skF_1') | ~m1_subset_1(A_5, '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1711])).
% 4.13/1.79  tff(c_1718, plain, (![A_216, A_217]: (k7_partfun1(A_216, '#skF_3', A_217)=k1_funct_1('#skF_3', A_217) | ~v5_relat_1('#skF_3', A_216) | ~m1_subset_1(A_217, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_1714])).
% 4.13/1.79  tff(c_1735, plain, (![A_220]: (k7_partfun1('#skF_2', '#skF_3', A_220)=k1_funct_1('#skF_3', A_220) | ~m1_subset_1(A_220, '#skF_1'))), inference(resolution, [status(thm)], [c_225, c_1718])).
% 4.13/1.79  tff(c_1746, plain, (k7_partfun1('#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_1735])).
% 4.13/1.79  tff(c_1752, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1408, c_1746])).
% 4.13/1.79  tff(c_1753, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1152])).
% 4.13/1.79  tff(c_38, plain, (![A_30]: (m1_subset_1(o_1_1_funct_2(A_30), A_30))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.13/1.79  tff(c_4, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.13/1.79  tff(c_62, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.13/1.79  tff(c_78, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(resolution, [status(thm)], [c_4, c_62])).
% 4.13/1.79  tff(c_102, plain, (![A_60, B_61]: (r2_hidden(A_60, B_61) | v1_xboole_0(B_61) | ~m1_subset_1(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.13/1.79  tff(c_14, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.13/1.79  tff(c_126, plain, (![B_67, A_68]: (~r1_tarski(B_67, A_68) | v1_xboole_0(B_67) | ~m1_subset_1(A_68, B_67))), inference(resolution, [status(thm)], [c_102, c_14])).
% 4.13/1.79  tff(c_138, plain, (![A_4]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_78, c_126])).
% 4.13/1.79  tff(c_140, plain, (![A_69]: (~m1_subset_1(A_69, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_138])).
% 4.13/1.79  tff(c_145, plain, $false, inference(resolution, [status(thm)], [c_38, c_140])).
% 4.13/1.79  tff(c_146, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_138])).
% 4.13/1.79  tff(c_1786, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1753, c_146])).
% 4.13/1.79  tff(c_1792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1786])).
% 4.13/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.79  
% 4.13/1.79  Inference rules
% 4.13/1.79  ----------------------
% 4.13/1.79  #Ref     : 0
% 4.13/1.79  #Sup     : 344
% 4.13/1.79  #Fact    : 0
% 4.13/1.79  #Define  : 0
% 4.13/1.79  #Split   : 15
% 4.13/1.79  #Chain   : 0
% 4.13/1.79  #Close   : 0
% 4.13/1.79  
% 4.13/1.79  Ordering : KBO
% 4.13/1.79  
% 4.13/1.79  Simplification rules
% 4.13/1.79  ----------------------
% 4.13/1.79  #Subsume      : 16
% 4.13/1.79  #Demod        : 235
% 4.13/1.79  #Tautology    : 122
% 4.13/1.79  #SimpNegUnit  : 7
% 4.13/1.79  #BackRed      : 58
% 4.13/1.79  
% 4.13/1.79  #Partial instantiations: 0
% 4.13/1.79  #Strategies tried      : 1
% 4.13/1.79  
% 4.13/1.79  Timing (in seconds)
% 4.13/1.79  ----------------------
% 4.13/1.79  Preprocessing        : 0.34
% 4.13/1.79  Parsing              : 0.19
% 4.13/1.79  CNF conversion       : 0.02
% 4.13/1.79  Main loop            : 0.58
% 4.13/1.79  Inferencing          : 0.20
% 4.13/1.79  Reduction            : 0.20
% 4.13/1.79  Demodulation         : 0.14
% 4.13/1.79  BG Simplification    : 0.03
% 4.13/1.79  Subsumption          : 0.10
% 4.13/1.79  Abstraction          : 0.02
% 4.13/1.79  MUC search           : 0.00
% 4.13/1.79  Cooper               : 0.00
% 4.13/1.79  Total                : 0.95
% 4.13/1.79  Index Insertion      : 0.00
% 4.13/1.79  Index Deletion       : 0.00
% 4.25/1.79  Index Matching       : 0.00
% 4.25/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
