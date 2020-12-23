%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:34 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 4.27s
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
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > o_1_0_wellord2 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(o_1_0_wellord2,type,(
    o_1_0_wellord2: $i > $i )).

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

tff(f_88,axiom,(
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

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(o_1_0_wellord2(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_1_0_wellord2)).

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

tff(c_1234,plain,(
    ! [A_192,B_193,C_194,D_195] :
      ( k3_funct_2(A_192,B_193,C_194,D_195) = k1_funct_1(C_194,D_195)
      | ~ m1_subset_1(D_195,A_192)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193)))
      | ~ v1_funct_2(C_194,A_192,B_193)
      | ~ v1_funct_1(C_194)
      | v1_xboole_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1248,plain,(
    ! [B_193,C_194] :
      ( k3_funct_2('#skF_1',B_193,C_194,'#skF_4') = k1_funct_1(C_194,'#skF_4')
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_193)))
      | ~ v1_funct_2(C_194,'#skF_1',B_193)
      | ~ v1_funct_1(C_194)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_1234])).

tff(c_1331,plain,(
    ! [B_200,C_201] :
      ( k3_funct_2('#skF_1',B_200,C_201,'#skF_4') = k1_funct_1(C_201,'#skF_4')
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_200)))
      | ~ v1_funct_2(C_201,'#skF_1',B_200)
      | ~ v1_funct_1(C_201) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1248])).

tff(c_1342,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1331])).

tff(c_1355,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1342])).

tff(c_42,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') != k7_partfun1('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1358,plain,(
    k7_partfun1('#skF_2','#skF_3','#skF_4') != k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1355,c_42])).

tff(c_350,plain,(
    ! [C_91,B_92,A_93] :
      ( v5_relat_1(C_91,B_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_367,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_350])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_104,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_87])).

tff(c_484,plain,(
    ! [A_123,B_124,C_125] :
      ( k1_relset_1(A_123,B_124,C_125) = k1_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_501,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_484])).

tff(c_1070,plain,(
    ! [B_174,A_175,C_176] :
      ( k1_xboole_0 = B_174
      | k1_relset_1(A_175,B_174,C_176) = A_175
      | ~ v1_funct_2(C_176,A_175,B_174)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_175,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1077,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_1070])).

tff(c_1089,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_501,c_1077])).

tff(c_1093,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1089])).

tff(c_1188,plain,(
    ! [A_184,B_185,C_186] :
      ( k7_partfun1(A_184,B_185,C_186) = k1_funct_1(B_185,C_186)
      | ~ r2_hidden(C_186,k1_relat_1(B_185))
      | ~ v1_funct_1(B_185)
      | ~ v5_relat_1(B_185,A_184)
      | ~ v1_relat_1(B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1190,plain,(
    ! [A_184,C_186] :
      ( k7_partfun1(A_184,'#skF_3',C_186) = k1_funct_1('#skF_3',C_186)
      | ~ r2_hidden(C_186,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_184)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_1188])).

tff(c_1695,plain,(
    ! [A_212,C_213] :
      ( k7_partfun1(A_212,'#skF_3',C_213) = k1_funct_1('#skF_3',C_213)
      | ~ r2_hidden(C_213,'#skF_1')
      | ~ v5_relat_1('#skF_3',A_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_50,c_1190])).

tff(c_1698,plain,(
    ! [A_212,A_5] :
      ( k7_partfun1(A_212,'#skF_3',A_5) = k1_funct_1('#skF_3',A_5)
      | ~ v5_relat_1('#skF_3',A_212)
      | v1_xboole_0('#skF_1')
      | ~ m1_subset_1(A_5,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6,c_1695])).

tff(c_1702,plain,(
    ! [A_214,A_215] :
      ( k7_partfun1(A_214,'#skF_3',A_215) = k1_funct_1('#skF_3',A_215)
      | ~ v5_relat_1('#skF_3',A_214)
      | ~ m1_subset_1(A_215,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1698])).

tff(c_1710,plain,(
    ! [A_216] :
      ( k7_partfun1('#skF_2','#skF_3',A_216) = k1_funct_1('#skF_3',A_216)
      | ~ m1_subset_1(A_216,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_367,c_1702])).

tff(c_1721,plain,(
    k7_partfun1('#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1710])).

tff(c_1727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1358,c_1721])).

tff(c_1728,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1089])).

tff(c_24,plain,(
    ! [A_23] : m1_subset_1(o_1_0_wellord2(A_23),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

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

tff(c_82,plain,(
    ! [A_57,B_58] :
      ( r2_hidden(A_57,B_58)
      | v1_xboole_0(B_58)
      | ~ m1_subset_1(A_57,B_58) ) ),
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
    inference(resolution,[status(thm)],[c_82,c_14])).

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
    inference(resolution,[status(thm)],[c_24,c_140])).

tff(c_146,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_1764,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1728,c_146])).

tff(c_1770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.89/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.67  
% 3.89/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.67  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > o_1_0_wellord2 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.89/1.67  
% 3.89/1.67  %Foreground sorts:
% 3.89/1.67  
% 3.89/1.67  
% 3.89/1.67  %Background operators:
% 3.89/1.67  
% 3.89/1.67  
% 3.89/1.67  %Foreground operators:
% 3.89/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.89/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.89/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.89/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.89/1.67  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.89/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.89/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.89/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.89/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.89/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.89/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.89/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.89/1.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.89/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.89/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.89/1.67  tff(o_1_0_wellord2, type, o_1_0_wellord2: $i > $i).
% 3.89/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.89/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.89/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.89/1.67  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.89/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.89/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.89/1.67  
% 3.89/1.69  tff(f_132, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 3.89/1.69  tff(f_112, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.89/1.69  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.89/1.69  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.89/1.69  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.89/1.69  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.89/1.69  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.89/1.69  tff(f_99, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 3.89/1.69  tff(f_70, axiom, (![A]: m1_subset_1(o_1_0_wellord2(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_1_0_wellord2)).
% 3.89/1.69  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.89/1.69  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.89/1.69  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.89/1.69  tff(c_52, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.89/1.69  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.89/1.69  tff(c_48, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.89/1.69  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.89/1.69  tff(c_54, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.89/1.69  tff(c_44, plain, (m1_subset_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.89/1.69  tff(c_1234, plain, (![A_192, B_193, C_194, D_195]: (k3_funct_2(A_192, B_193, C_194, D_195)=k1_funct_1(C_194, D_195) | ~m1_subset_1(D_195, A_192) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))) | ~v1_funct_2(C_194, A_192, B_193) | ~v1_funct_1(C_194) | v1_xboole_0(A_192))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.89/1.69  tff(c_1248, plain, (![B_193, C_194]: (k3_funct_2('#skF_1', B_193, C_194, '#skF_4')=k1_funct_1(C_194, '#skF_4') | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_193))) | ~v1_funct_2(C_194, '#skF_1', B_193) | ~v1_funct_1(C_194) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_1234])).
% 3.89/1.69  tff(c_1331, plain, (![B_200, C_201]: (k3_funct_2('#skF_1', B_200, C_201, '#skF_4')=k1_funct_1(C_201, '#skF_4') | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_200))) | ~v1_funct_2(C_201, '#skF_1', B_200) | ~v1_funct_1(C_201))), inference(negUnitSimplification, [status(thm)], [c_54, c_1248])).
% 3.89/1.69  tff(c_1342, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1331])).
% 3.89/1.69  tff(c_1355, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1342])).
% 3.89/1.69  tff(c_42, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k7_partfun1('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.89/1.69  tff(c_1358, plain, (k7_partfun1('#skF_2', '#skF_3', '#skF_4')!=k1_funct_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1355, c_42])).
% 3.89/1.69  tff(c_350, plain, (![C_91, B_92, A_93]: (v5_relat_1(C_91, B_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.89/1.69  tff(c_367, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_350])).
% 3.89/1.69  tff(c_6, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.89/1.69  tff(c_87, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.89/1.69  tff(c_104, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_87])).
% 3.89/1.69  tff(c_484, plain, (![A_123, B_124, C_125]: (k1_relset_1(A_123, B_124, C_125)=k1_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.89/1.69  tff(c_501, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_484])).
% 3.89/1.69  tff(c_1070, plain, (![B_174, A_175, C_176]: (k1_xboole_0=B_174 | k1_relset_1(A_175, B_174, C_176)=A_175 | ~v1_funct_2(C_176, A_175, B_174) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_175, B_174))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.89/1.69  tff(c_1077, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_1070])).
% 3.89/1.69  tff(c_1089, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_501, c_1077])).
% 3.89/1.69  tff(c_1093, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1089])).
% 3.89/1.69  tff(c_1188, plain, (![A_184, B_185, C_186]: (k7_partfun1(A_184, B_185, C_186)=k1_funct_1(B_185, C_186) | ~r2_hidden(C_186, k1_relat_1(B_185)) | ~v1_funct_1(B_185) | ~v5_relat_1(B_185, A_184) | ~v1_relat_1(B_185))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.89/1.69  tff(c_1190, plain, (![A_184, C_186]: (k7_partfun1(A_184, '#skF_3', C_186)=k1_funct_1('#skF_3', C_186) | ~r2_hidden(C_186, '#skF_1') | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', A_184) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1093, c_1188])).
% 3.89/1.69  tff(c_1695, plain, (![A_212, C_213]: (k7_partfun1(A_212, '#skF_3', C_213)=k1_funct_1('#skF_3', C_213) | ~r2_hidden(C_213, '#skF_1') | ~v5_relat_1('#skF_3', A_212))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_50, c_1190])).
% 3.89/1.69  tff(c_1698, plain, (![A_212, A_5]: (k7_partfun1(A_212, '#skF_3', A_5)=k1_funct_1('#skF_3', A_5) | ~v5_relat_1('#skF_3', A_212) | v1_xboole_0('#skF_1') | ~m1_subset_1(A_5, '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1695])).
% 3.89/1.69  tff(c_1702, plain, (![A_214, A_215]: (k7_partfun1(A_214, '#skF_3', A_215)=k1_funct_1('#skF_3', A_215) | ~v5_relat_1('#skF_3', A_214) | ~m1_subset_1(A_215, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_1698])).
% 3.89/1.69  tff(c_1710, plain, (![A_216]: (k7_partfun1('#skF_2', '#skF_3', A_216)=k1_funct_1('#skF_3', A_216) | ~m1_subset_1(A_216, '#skF_1'))), inference(resolution, [status(thm)], [c_367, c_1702])).
% 3.89/1.69  tff(c_1721, plain, (k7_partfun1('#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_1710])).
% 3.89/1.69  tff(c_1727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1358, c_1721])).
% 3.89/1.69  tff(c_1728, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1089])).
% 3.89/1.69  tff(c_24, plain, (![A_23]: (m1_subset_1(o_1_0_wellord2(A_23), A_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.89/1.69  tff(c_4, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.89/1.69  tff(c_62, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.89/1.69  tff(c_78, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(resolution, [status(thm)], [c_4, c_62])).
% 3.89/1.69  tff(c_82, plain, (![A_57, B_58]: (r2_hidden(A_57, B_58) | v1_xboole_0(B_58) | ~m1_subset_1(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.89/1.69  tff(c_14, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.27/1.69  tff(c_126, plain, (![B_67, A_68]: (~r1_tarski(B_67, A_68) | v1_xboole_0(B_67) | ~m1_subset_1(A_68, B_67))), inference(resolution, [status(thm)], [c_82, c_14])).
% 4.27/1.69  tff(c_138, plain, (![A_4]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_78, c_126])).
% 4.27/1.69  tff(c_140, plain, (![A_69]: (~m1_subset_1(A_69, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_138])).
% 4.27/1.69  tff(c_145, plain, $false, inference(resolution, [status(thm)], [c_24, c_140])).
% 4.27/1.69  tff(c_146, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_138])).
% 4.27/1.69  tff(c_1764, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1728, c_146])).
% 4.27/1.69  tff(c_1770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1764])).
% 4.27/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.69  
% 4.27/1.69  Inference rules
% 4.27/1.69  ----------------------
% 4.27/1.69  #Ref     : 0
% 4.27/1.69  #Sup     : 340
% 4.27/1.69  #Fact    : 0
% 4.27/1.69  #Define  : 0
% 4.27/1.69  #Split   : 16
% 4.27/1.69  #Chain   : 0
% 4.27/1.69  #Close   : 0
% 4.27/1.69  
% 4.27/1.69  Ordering : KBO
% 4.27/1.69  
% 4.27/1.69  Simplification rules
% 4.27/1.69  ----------------------
% 4.27/1.69  #Subsume      : 16
% 4.27/1.69  #Demod        : 232
% 4.27/1.69  #Tautology    : 120
% 4.27/1.69  #SimpNegUnit  : 7
% 4.27/1.69  #BackRed      : 56
% 4.27/1.69  
% 4.27/1.69  #Partial instantiations: 0
% 4.27/1.69  #Strategies tried      : 1
% 4.27/1.69  
% 4.27/1.69  Timing (in seconds)
% 4.27/1.69  ----------------------
% 4.27/1.69  Preprocessing        : 0.34
% 4.27/1.69  Parsing              : 0.18
% 4.27/1.69  CNF conversion       : 0.02
% 4.27/1.69  Main loop            : 0.60
% 4.27/1.69  Inferencing          : 0.20
% 4.27/1.69  Reduction            : 0.21
% 4.27/1.69  Demodulation         : 0.15
% 4.27/1.69  BG Simplification    : 0.03
% 4.27/1.69  Subsumption          : 0.11
% 4.27/1.69  Abstraction          : 0.03
% 4.27/1.69  MUC search           : 0.00
% 4.27/1.69  Cooper               : 0.00
% 4.27/1.69  Total                : 0.97
% 4.27/1.69  Index Insertion      : 0.00
% 4.27/1.69  Index Deletion       : 0.00
% 4.27/1.69  Index Matching       : 0.00
% 4.27/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
