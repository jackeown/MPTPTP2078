%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:28 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 8.06s
% Verified   : 
% Statistics : Number of formulae       :  206 (3195 expanded)
%              Number of leaves         :   36 (1116 expanded)
%              Depth                    :   23
%              Number of atoms          :  487 (10467 expanded)
%              Number of equality atoms :  167 (4148 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_102,plain,(
    ! [A_87,B_88,C_89] :
      ( k2_relset_1(A_87,B_88,C_89) = k2_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_106,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_102])).

tff(c_127,plain,(
    ! [A_97,B_98,C_99] :
      ( m1_subset_1(k2_relset_1(A_97,B_98,C_99),k1_zfmisc_1(B_98))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_143,plain,
    ( m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_127])).

tff(c_149,plain,(
    m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_143])).

tff(c_6,plain,(
    ! [B_8,A_6] :
      ( v1_relat_1(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_169,plain,
    ( v1_relat_1(k2_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_149,c_6])).

tff(c_170,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_52,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_48,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_107,plain,(
    k2_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_48])).

tff(c_8,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_77,plain,(
    ! [B_78,A_79] :
      ( v1_relat_1(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79))
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_50,c_77])).

tff(c_83,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_80])).

tff(c_54,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_117,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_121,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_117])).

tff(c_245,plain,(
    ! [B_121,A_122,C_123] :
      ( k1_xboole_0 = B_121
      | k1_relset_1(A_122,B_121,C_123) = A_122
      | ~ v1_funct_2(C_123,A_122,B_121)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_252,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_245])).

tff(c_256,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_121,c_252])).

tff(c_257,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_357,plain,(
    ! [A_146,B_147] :
      ( r2_hidden('#skF_2'(A_146,B_147),k1_relat_1(A_146))
      | r2_hidden('#skF_3'(A_146,B_147),B_147)
      | k2_relat_1(A_146) = B_147
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_370,plain,(
    ! [B_147] :
      ( r2_hidden('#skF_2'('#skF_7',B_147),'#skF_5')
      | r2_hidden('#skF_3'('#skF_7',B_147),B_147)
      | k2_relat_1('#skF_7') = B_147
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_357])).

tff(c_376,plain,(
    ! [B_147] :
      ( r2_hidden('#skF_2'('#skF_7',B_147),'#skF_5')
      | r2_hidden('#skF_3'('#skF_7',B_147),B_147)
      | k2_relat_1('#skF_7') = B_147 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_370])).

tff(c_58,plain,(
    ! [D_68] :
      ( r2_hidden('#skF_8'(D_68),'#skF_5')
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_56,plain,(
    ! [D_68] :
      ( k1_funct_1('#skF_7','#skF_8'(D_68)) = D_68
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_593,plain,(
    ! [A_172,B_173,D_174] :
      ( r2_hidden('#skF_2'(A_172,B_173),k1_relat_1(A_172))
      | k1_funct_1(A_172,D_174) != '#skF_3'(A_172,B_173)
      | ~ r2_hidden(D_174,k1_relat_1(A_172))
      | k2_relat_1(A_172) = B_173
      | ~ v1_funct_1(A_172)
      | ~ v1_relat_1(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_599,plain,(
    ! [B_173,D_68] :
      ( r2_hidden('#skF_2'('#skF_7',B_173),k1_relat_1('#skF_7'))
      | D_68 != '#skF_3'('#skF_7',B_173)
      | ~ r2_hidden('#skF_8'(D_68),k1_relat_1('#skF_7'))
      | k2_relat_1('#skF_7') = B_173
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_593])).

tff(c_601,plain,(
    ! [B_173,D_68] :
      ( r2_hidden('#skF_2'('#skF_7',B_173),'#skF_5')
      | D_68 != '#skF_3'('#skF_7',B_173)
      | ~ r2_hidden('#skF_8'(D_68),'#skF_5')
      | k2_relat_1('#skF_7') = B_173
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_257,c_257,c_599])).

tff(c_1225,plain,(
    ! [B_249] :
      ( r2_hidden('#skF_2'('#skF_7',B_249),'#skF_5')
      | ~ r2_hidden('#skF_8'('#skF_3'('#skF_7',B_249)),'#skF_5')
      | k2_relat_1('#skF_7') = B_249
      | ~ r2_hidden('#skF_3'('#skF_7',B_249),'#skF_6') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_601])).

tff(c_1234,plain,(
    ! [B_250] :
      ( r2_hidden('#skF_2'('#skF_7',B_250),'#skF_5')
      | k2_relat_1('#skF_7') = B_250
      | ~ r2_hidden('#skF_3'('#skF_7',B_250),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_1225])).

tff(c_1254,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_5')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_376,c_1234])).

tff(c_1272,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_107,c_1254])).

tff(c_24,plain,(
    ! [A_11,B_33] :
      ( k1_funct_1(A_11,'#skF_2'(A_11,B_33)) = '#skF_1'(A_11,B_33)
      | r2_hidden('#skF_3'(A_11,B_33),B_33)
      | k2_relat_1(A_11) = B_33
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_686,plain,(
    ! [A_190,B_191,D_192] :
      ( k1_funct_1(A_190,'#skF_2'(A_190,B_191)) = '#skF_1'(A_190,B_191)
      | k1_funct_1(A_190,D_192) != '#skF_3'(A_190,B_191)
      | ~ r2_hidden(D_192,k1_relat_1(A_190))
      | k2_relat_1(A_190) = B_191
      | ~ v1_funct_1(A_190)
      | ~ v1_relat_1(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_692,plain,(
    ! [B_191,D_68] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_191)) = '#skF_1'('#skF_7',B_191)
      | D_68 != '#skF_3'('#skF_7',B_191)
      | ~ r2_hidden('#skF_8'(D_68),k1_relat_1('#skF_7'))
      | k2_relat_1('#skF_7') = B_191
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_686])).

tff(c_694,plain,(
    ! [B_191,D_68] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_191)) = '#skF_1'('#skF_7',B_191)
      | D_68 != '#skF_3'('#skF_7',B_191)
      | ~ r2_hidden('#skF_8'(D_68),'#skF_5')
      | k2_relat_1('#skF_7') = B_191
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_257,c_692])).

tff(c_1869,plain,(
    ! [B_367] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_367)) = '#skF_1'('#skF_7',B_367)
      | ~ r2_hidden('#skF_8'('#skF_3'('#skF_7',B_367)),'#skF_5')
      | k2_relat_1('#skF_7') = B_367
      | ~ r2_hidden('#skF_3'('#skF_7',B_367),'#skF_6') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_694])).

tff(c_1878,plain,(
    ! [B_368] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_368)) = '#skF_1'('#skF_7',B_368)
      | k2_relat_1('#skF_7') = B_368
      | ~ r2_hidden('#skF_3'('#skF_7',B_368),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_1869])).

tff(c_1916,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_6')) = '#skF_1'('#skF_7','#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_1878])).

tff(c_1947,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_6')) = '#skF_1'('#skF_7','#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_1916])).

tff(c_1948,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_6')) = '#skF_1'('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_1947])).

tff(c_150,plain,(
    ! [A_100,D_101] :
      ( r2_hidden(k1_funct_1(A_100,D_101),k2_relat_1(A_100))
      | ~ r2_hidden(D_101,k1_relat_1(A_100))
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [C_5,A_2,B_3] :
      ( r2_hidden(C_5,A_2)
      | ~ r2_hidden(C_5,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_630,plain,(
    ! [A_183,D_184,A_185] :
      ( r2_hidden(k1_funct_1(A_183,D_184),A_185)
      | ~ m1_subset_1(k2_relat_1(A_183),k1_zfmisc_1(A_185))
      | ~ r2_hidden(D_184,k1_relat_1(A_183))
      | ~ v1_funct_1(A_183)
      | ~ v1_relat_1(A_183) ) ),
    inference(resolution,[status(thm)],[c_150,c_4])).

tff(c_632,plain,(
    ! [D_184] :
      ( r2_hidden(k1_funct_1('#skF_7',D_184),'#skF_6')
      | ~ r2_hidden(D_184,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_149,c_630])).

tff(c_635,plain,(
    ! [D_184] :
      ( r2_hidden(k1_funct_1('#skF_7',D_184),'#skF_6')
      | ~ r2_hidden(D_184,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_257,c_632])).

tff(c_1971,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1948,c_635])).

tff(c_1994,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1272,c_1971])).

tff(c_22,plain,(
    ! [A_11,B_33] :
      ( ~ r2_hidden('#skF_1'(A_11,B_33),B_33)
      | r2_hidden('#skF_3'(A_11,B_33),B_33)
      | k2_relat_1(A_11) = B_33
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_158,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_8'(D_68),k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_150])).

tff(c_162,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_8'(D_68),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_158])).

tff(c_280,plain,(
    ! [D_124] :
      ( r2_hidden(D_124,k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_8'(D_124),'#skF_5')
      | ~ r2_hidden(D_124,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_162])).

tff(c_289,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,k2_relat_1('#skF_7'))
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_280])).

tff(c_12,plain,(
    ! [A_11,C_47] :
      ( k1_funct_1(A_11,'#skF_4'(A_11,k2_relat_1(A_11),C_47)) = C_47
      | ~ r2_hidden(C_47,k2_relat_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_11,C_47] :
      ( r2_hidden('#skF_4'(A_11,k2_relat_1(A_11),C_47),k1_relat_1(A_11))
      | ~ r2_hidden(C_47,k2_relat_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_268,plain,(
    ! [C_47] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_47),'#skF_5')
      | ~ r2_hidden(C_47,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_14])).

tff(c_274,plain,(
    ! [C_47] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_47),'#skF_5')
      | ~ r2_hidden(C_47,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_268])).

tff(c_16,plain,(
    ! [A_11,B_33,D_46] :
      ( ~ r2_hidden('#skF_1'(A_11,B_33),B_33)
      | k1_funct_1(A_11,D_46) != '#skF_3'(A_11,B_33)
      | ~ r2_hidden(D_46,k1_relat_1(A_11))
      | k2_relat_1(A_11) = B_33
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2005,plain,(
    ! [D_46] :
      ( k1_funct_1('#skF_7',D_46) != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(D_46,k1_relat_1('#skF_7'))
      | k2_relat_1('#skF_7') = '#skF_6'
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1994,c_16])).

tff(c_2020,plain,(
    ! [D_46] :
      ( k1_funct_1('#skF_7',D_46) != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(D_46,'#skF_5')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_257,c_2005])).

tff(c_2132,plain,(
    ! [D_375] :
      ( k1_funct_1('#skF_7',D_375) != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(D_375,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_2020])).

tff(c_2520,plain,(
    ! [C_395] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_395)) != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(C_395,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_274,c_2132])).

tff(c_2524,plain,(
    ! [C_47] :
      ( C_47 != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(C_47,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_47,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2520])).

tff(c_2528,plain,(
    ! [C_396] :
      ( C_396 != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(C_396,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_2524])).

tff(c_2673,plain,(
    ! [D_397] :
      ( D_397 != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(D_397,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_289,c_2528])).

tff(c_3639,plain,(
    ! [A_467] :
      ( '#skF_3'(A_467,'#skF_6') != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden('#skF_1'(A_467,'#skF_6'),'#skF_6')
      | k2_relat_1(A_467) = '#skF_6'
      | ~ v1_funct_1(A_467)
      | ~ v1_relat_1(A_467) ) ),
    inference(resolution,[status(thm)],[c_22,c_2673])).

tff(c_3654,plain,
    ( k2_relat_1('#skF_7') = '#skF_6'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1994,c_3639])).

tff(c_3669,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_3654])).

tff(c_3671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_3669])).

tff(c_3672,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_38,plain,(
    ! [C_64,A_62] :
      ( k1_xboole_0 = C_64
      | ~ v1_funct_2(C_64,A_62,k1_xboole_0)
      | k1_xboole_0 = A_62
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3704,plain,(
    ! [C_473,A_474] :
      ( C_473 = '#skF_6'
      | ~ v1_funct_2(C_473,A_474,'#skF_6')
      | A_474 = '#skF_6'
      | ~ m1_subset_1(C_473,k1_zfmisc_1(k2_zfmisc_1(A_474,'#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3672,c_3672,c_3672,c_3672,c_38])).

tff(c_3711,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50,c_3704])).

tff(c_3715,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3711])).

tff(c_3716,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3715])).

tff(c_3673,plain,(
    k1_relat_1('#skF_7') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_3718,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3716,c_3673])).

tff(c_3730,plain,(
    v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3716,c_52])).

tff(c_3722,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3716,c_121])).

tff(c_3729,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3716,c_50])).

tff(c_44,plain,(
    ! [B_63,C_64] :
      ( k1_relset_1(k1_xboole_0,B_63,C_64) = k1_xboole_0
      | ~ v1_funct_2(C_64,k1_xboole_0,B_63)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3825,plain,(
    ! [B_482,C_483] :
      ( k1_relset_1('#skF_6',B_482,C_483) = '#skF_6'
      | ~ v1_funct_2(C_483,'#skF_6',B_482)
      | ~ m1_subset_1(C_483,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_482))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3672,c_3672,c_3672,c_3672,c_44])).

tff(c_3828,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_7') = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_3729,c_3825])).

tff(c_3835,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3730,c_3722,c_3828])).

tff(c_3837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3718,c_3835])).

tff(c_3838,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3715])).

tff(c_3850,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3838,c_83])).

tff(c_3856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_3850])).

tff(c_3858,plain,(
    v1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_3958,plain,(
    ! [B_512,A_513,C_514] :
      ( k1_xboole_0 = B_512
      | k1_relset_1(A_513,B_512,C_514) = A_513
      | ~ v1_funct_2(C_514,A_513,B_512)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(k2_zfmisc_1(A_513,B_512))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3965,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_3958])).

tff(c_3969,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_121,c_3965])).

tff(c_3970,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3969])).

tff(c_4003,plain,(
    ! [A_516,B_517] :
      ( r2_hidden('#skF_2'(A_516,B_517),k1_relat_1(A_516))
      | r2_hidden('#skF_3'(A_516,B_517),B_517)
      | k2_relat_1(A_516) = B_517
      | ~ v1_funct_1(A_516)
      | ~ v1_relat_1(A_516) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4016,plain,(
    ! [B_517] :
      ( r2_hidden('#skF_2'('#skF_7',B_517),'#skF_5')
      | r2_hidden('#skF_3'('#skF_7',B_517),B_517)
      | k2_relat_1('#skF_7') = B_517
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3970,c_4003])).

tff(c_4022,plain,(
    ! [B_517] :
      ( r2_hidden('#skF_2'('#skF_7',B_517),'#skF_5')
      | r2_hidden('#skF_3'('#skF_7',B_517),B_517)
      | k2_relat_1('#skF_7') = B_517 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_4016])).

tff(c_4306,plain,(
    ! [A_551,B_552,D_553] :
      ( r2_hidden('#skF_2'(A_551,B_552),k1_relat_1(A_551))
      | k1_funct_1(A_551,D_553) != '#skF_3'(A_551,B_552)
      | ~ r2_hidden(D_553,k1_relat_1(A_551))
      | k2_relat_1(A_551) = B_552
      | ~ v1_funct_1(A_551)
      | ~ v1_relat_1(A_551) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4312,plain,(
    ! [B_552,D_68] :
      ( r2_hidden('#skF_2'('#skF_7',B_552),k1_relat_1('#skF_7'))
      | D_68 != '#skF_3'('#skF_7',B_552)
      | ~ r2_hidden('#skF_8'(D_68),k1_relat_1('#skF_7'))
      | k2_relat_1('#skF_7') = B_552
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_4306])).

tff(c_4314,plain,(
    ! [B_552,D_68] :
      ( r2_hidden('#skF_2'('#skF_7',B_552),'#skF_5')
      | D_68 != '#skF_3'('#skF_7',B_552)
      | ~ r2_hidden('#skF_8'(D_68),'#skF_5')
      | k2_relat_1('#skF_7') = B_552
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_3970,c_3970,c_4312])).

tff(c_4939,plain,(
    ! [B_635] :
      ( r2_hidden('#skF_2'('#skF_7',B_635),'#skF_5')
      | ~ r2_hidden('#skF_8'('#skF_3'('#skF_7',B_635)),'#skF_5')
      | k2_relat_1('#skF_7') = B_635
      | ~ r2_hidden('#skF_3'('#skF_7',B_635),'#skF_6') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4314])).

tff(c_4948,plain,(
    ! [B_636] :
      ( r2_hidden('#skF_2'('#skF_7',B_636),'#skF_5')
      | k2_relat_1('#skF_7') = B_636
      | ~ r2_hidden('#skF_3'('#skF_7',B_636),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_4939])).

tff(c_4972,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_5')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_4022,c_4948])).

tff(c_4994,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_107,c_4972])).

tff(c_4381,plain,(
    ! [A_569,B_570,D_571] :
      ( k1_funct_1(A_569,'#skF_2'(A_569,B_570)) = '#skF_1'(A_569,B_570)
      | k1_funct_1(A_569,D_571) != '#skF_3'(A_569,B_570)
      | ~ r2_hidden(D_571,k1_relat_1(A_569))
      | k2_relat_1(A_569) = B_570
      | ~ v1_funct_1(A_569)
      | ~ v1_relat_1(A_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4387,plain,(
    ! [B_570,D_68] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_570)) = '#skF_1'('#skF_7',B_570)
      | D_68 != '#skF_3'('#skF_7',B_570)
      | ~ r2_hidden('#skF_8'(D_68),k1_relat_1('#skF_7'))
      | k2_relat_1('#skF_7') = B_570
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_4381])).

tff(c_4389,plain,(
    ! [B_570,D_68] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_570)) = '#skF_1'('#skF_7',B_570)
      | D_68 != '#skF_3'('#skF_7',B_570)
      | ~ r2_hidden('#skF_8'(D_68),'#skF_5')
      | k2_relat_1('#skF_7') = B_570
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_3970,c_4387])).

tff(c_5237,plain,(
    ! [B_681] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_681)) = '#skF_1'('#skF_7',B_681)
      | ~ r2_hidden('#skF_8'('#skF_3'('#skF_7',B_681)),'#skF_5')
      | k2_relat_1('#skF_7') = B_681
      | ~ r2_hidden('#skF_3'('#skF_7',B_681),'#skF_6') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4389])).

tff(c_5246,plain,(
    ! [B_682] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_682)) = '#skF_1'('#skF_7',B_682)
      | k2_relat_1('#skF_7') = B_682
      | ~ r2_hidden('#skF_3'('#skF_7',B_682),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_5237])).

tff(c_5272,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_6')) = '#skF_1'('#skF_7','#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_5246])).

tff(c_5295,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_6')) = '#skF_1'('#skF_7','#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_5272])).

tff(c_5296,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_6')) = '#skF_1'('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_5295])).

tff(c_4414,plain,(
    ! [A_578,D_579,A_580] :
      ( r2_hidden(k1_funct_1(A_578,D_579),A_580)
      | ~ m1_subset_1(k2_relat_1(A_578),k1_zfmisc_1(A_580))
      | ~ r2_hidden(D_579,k1_relat_1(A_578))
      | ~ v1_funct_1(A_578)
      | ~ v1_relat_1(A_578) ) ),
    inference(resolution,[status(thm)],[c_150,c_4])).

tff(c_4416,plain,(
    ! [D_579] :
      ( r2_hidden(k1_funct_1('#skF_7',D_579),'#skF_6')
      | ~ r2_hidden(D_579,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_149,c_4414])).

tff(c_4419,plain,(
    ! [D_579] :
      ( r2_hidden(k1_funct_1('#skF_7',D_579),'#skF_6')
      | ~ r2_hidden(D_579,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_3970,c_4416])).

tff(c_5316,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5296,c_4419])).

tff(c_5338,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4994,c_5316])).

tff(c_3993,plain,(
    ! [D_515] :
      ( r2_hidden(D_515,k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_8'(D_515),'#skF_5')
      | ~ r2_hidden(D_515,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3970,c_162])).

tff(c_4002,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,k2_relat_1('#skF_7'))
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_3993])).

tff(c_3981,plain,(
    ! [C_47] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_47),'#skF_5')
      | ~ r2_hidden(C_47,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3970,c_14])).

tff(c_3987,plain,(
    ! [C_47] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_47),'#skF_5')
      | ~ r2_hidden(C_47,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_3981])).

tff(c_5354,plain,(
    ! [D_46] :
      ( k1_funct_1('#skF_7',D_46) != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(D_46,k1_relat_1('#skF_7'))
      | k2_relat_1('#skF_7') = '#skF_6'
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5338,c_16])).

tff(c_5370,plain,(
    ! [D_46] :
      ( k1_funct_1('#skF_7',D_46) != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(D_46,'#skF_5')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_3970,c_5354])).

tff(c_5516,plain,(
    ! [D_687] :
      ( k1_funct_1('#skF_7',D_687) != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(D_687,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_5370])).

tff(c_5875,plain,(
    ! [C_710] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_710)) != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(C_710,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_3987,c_5516])).

tff(c_5879,plain,(
    ! [C_47] :
      ( C_47 != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(C_47,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_47,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5875])).

tff(c_5883,plain,(
    ! [C_711] :
      ( C_711 != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(C_711,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_5879])).

tff(c_6018,plain,(
    ! [D_712] :
      ( D_712 != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(D_712,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4002,c_5883])).

tff(c_6919,plain,(
    ! [A_783] :
      ( '#skF_3'(A_783,'#skF_6') != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden('#skF_1'(A_783,'#skF_6'),'#skF_6')
      | k2_relat_1(A_783) = '#skF_6'
      | ~ v1_funct_1(A_783)
      | ~ v1_relat_1(A_783) ) ),
    inference(resolution,[status(thm)],[c_22,c_6018])).

tff(c_6934,plain,
    ( k2_relat_1('#skF_7') = '#skF_6'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_5338,c_6919])).

tff(c_6949,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_54,c_6934])).

tff(c_6951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_6949])).

tff(c_6952,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3969])).

tff(c_6973,plain,(
    ! [C_786,A_787] :
      ( C_786 = '#skF_6'
      | ~ v1_funct_2(C_786,A_787,'#skF_6')
      | A_787 = '#skF_6'
      | ~ m1_subset_1(C_786,k1_zfmisc_1(k2_zfmisc_1(A_787,'#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6952,c_6952,c_6952,c_6952,c_38])).

tff(c_6980,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50,c_6973])).

tff(c_6984,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6980])).

tff(c_6985,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6984])).

tff(c_6953,plain,(
    k1_relat_1('#skF_7') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3969])).

tff(c_6987,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6985,c_6953])).

tff(c_7000,plain,(
    v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6985,c_52])).

tff(c_6992,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6985,c_121])).

tff(c_6999,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6985,c_50])).

tff(c_7102,plain,(
    ! [B_793,C_794] :
      ( k1_relset_1('#skF_6',B_793,C_794) = '#skF_6'
      | ~ v1_funct_2(C_794,'#skF_6',B_793)
      | ~ m1_subset_1(C_794,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_793))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6952,c_6952,c_6952,c_6952,c_44])).

tff(c_7105,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_7') = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_6999,c_7102])).

tff(c_7112,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7000,c_6992,c_7105])).

tff(c_7114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6987,c_7112])).

tff(c_7115,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6984])).

tff(c_7132,plain,(
    v1_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7115,c_54])).

tff(c_26,plain,(
    ! [A_11,B_33] :
      ( r2_hidden('#skF_2'(A_11,B_33),k1_relat_1(A_11))
      | r2_hidden('#skF_3'(A_11,B_33),B_33)
      | k2_relat_1(A_11) = B_33
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6961,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6952,c_2])).

tff(c_7124,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7115,c_149])).

tff(c_7317,plain,(
    ! [A_822,D_823,A_824] :
      ( r2_hidden(k1_funct_1(A_822,D_823),A_824)
      | ~ m1_subset_1(k2_relat_1(A_822),k1_zfmisc_1(A_824))
      | ~ r2_hidden(D_823,k1_relat_1(A_822))
      | ~ v1_funct_1(A_822)
      | ~ v1_relat_1(A_822) ) ),
    inference(resolution,[status(thm)],[c_150,c_4])).

tff(c_7319,plain,(
    ! [D_823] :
      ( r2_hidden(k1_funct_1('#skF_6',D_823),'#skF_6')
      | ~ r2_hidden(D_823,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_7124,c_7317])).

tff(c_7323,plain,(
    ! [D_825] :
      ( r2_hidden(k1_funct_1('#skF_6',D_825),'#skF_6')
      | ~ r2_hidden(D_825,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3858,c_7132,c_7319])).

tff(c_28,plain,(
    ! [B_52,A_51] :
      ( ~ r1_tarski(B_52,A_51)
      | ~ r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7328,plain,(
    ! [D_825] :
      ( ~ r1_tarski('#skF_6',k1_funct_1('#skF_6',D_825))
      | ~ r2_hidden(D_825,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_7323,c_28])).

tff(c_7353,plain,(
    ! [D_829] : ~ r2_hidden(D_829,k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6961,c_7328])).

tff(c_7361,plain,(
    ! [B_33] :
      ( r2_hidden('#skF_3'('#skF_6',B_33),B_33)
      | k2_relat_1('#skF_6') = B_33
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_7353])).

tff(c_7416,plain,(
    ! [B_831] :
      ( r2_hidden('#skF_3'('#skF_6',B_831),B_831)
      | k2_relat_1('#skF_6') = B_831 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3858,c_7132,c_7361])).

tff(c_7341,plain,(
    ! [D_825] : ~ r2_hidden(D_825,k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6961,c_7328])).

tff(c_7432,plain,(
    k2_relat_1('#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_7416,c_7341])).

tff(c_7126,plain,(
    k2_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7115,c_107])).

tff(c_7442,plain,(
    k1_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7432,c_7126])).

tff(c_7434,plain,(
    ! [B_831] :
      ( ~ r1_tarski(B_831,'#skF_3'('#skF_6',B_831))
      | k2_relat_1('#skF_6') = B_831 ) ),
    inference(resolution,[status(thm)],[c_7416,c_28])).

tff(c_7506,plain,(
    ! [B_834] :
      ( ~ r1_tarski(B_834,'#skF_3'('#skF_6',B_834))
      | k1_relat_1('#skF_6') = B_834 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7432,c_7434])).

tff(c_7510,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6961,c_7506])).

tff(c_7514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7442,c_7510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:32:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.73/2.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.06/2.66  
% 8.06/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.06/2.67  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 8.06/2.67  
% 8.06/2.67  %Foreground sorts:
% 8.06/2.67  
% 8.06/2.67  
% 8.06/2.67  %Background operators:
% 8.06/2.67  
% 8.06/2.67  
% 8.06/2.67  %Foreground operators:
% 8.06/2.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.06/2.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.06/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.06/2.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.06/2.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.06/2.67  tff('#skF_8', type, '#skF_8': $i > $i).
% 8.06/2.67  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.06/2.67  tff('#skF_7', type, '#skF_7': $i).
% 8.06/2.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.06/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.06/2.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.06/2.67  tff('#skF_5', type, '#skF_5': $i).
% 8.06/2.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.06/2.67  tff('#skF_6', type, '#skF_6': $i).
% 8.06/2.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.06/2.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.06/2.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.06/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.06/2.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.06/2.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.06/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.06/2.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.06/2.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.06/2.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.06/2.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.06/2.67  
% 8.06/2.69  tff(f_112, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 8.06/2.69  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.06/2.69  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 8.06/2.69  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.06/2.69  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.06/2.69  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.06/2.69  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.06/2.69  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 8.06/2.69  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 8.06/2.69  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.06/2.69  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.06/2.69  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.06/2.69  tff(c_102, plain, (![A_87, B_88, C_89]: (k2_relset_1(A_87, B_88, C_89)=k2_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.06/2.69  tff(c_106, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_50, c_102])).
% 8.06/2.69  tff(c_127, plain, (![A_97, B_98, C_99]: (m1_subset_1(k2_relset_1(A_97, B_98, C_99), k1_zfmisc_1(B_98)) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.06/2.69  tff(c_143, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_106, c_127])).
% 8.06/2.69  tff(c_149, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_143])).
% 8.06/2.69  tff(c_6, plain, (![B_8, A_6]: (v1_relat_1(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.06/2.69  tff(c_169, plain, (v1_relat_1(k2_relat_1('#skF_7')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_149, c_6])).
% 8.06/2.69  tff(c_170, plain, (~v1_relat_1('#skF_6')), inference(splitLeft, [status(thm)], [c_169])).
% 8.06/2.69  tff(c_52, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.06/2.69  tff(c_48, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.06/2.69  tff(c_107, plain, (k2_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_48])).
% 8.06/2.69  tff(c_8, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.06/2.69  tff(c_77, plain, (![B_78, A_79]: (v1_relat_1(B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.06/2.69  tff(c_80, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_50, c_77])).
% 8.06/2.69  tff(c_83, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_80])).
% 8.06/2.69  tff(c_54, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.06/2.69  tff(c_117, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.06/2.69  tff(c_121, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_50, c_117])).
% 8.06/2.69  tff(c_245, plain, (![B_121, A_122, C_123]: (k1_xboole_0=B_121 | k1_relset_1(A_122, B_121, C_123)=A_122 | ~v1_funct_2(C_123, A_122, B_121) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.06/2.69  tff(c_252, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_245])).
% 8.06/2.69  tff(c_256, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_121, c_252])).
% 8.06/2.69  tff(c_257, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_256])).
% 8.06/2.69  tff(c_357, plain, (![A_146, B_147]: (r2_hidden('#skF_2'(A_146, B_147), k1_relat_1(A_146)) | r2_hidden('#skF_3'(A_146, B_147), B_147) | k2_relat_1(A_146)=B_147 | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.06/2.69  tff(c_370, plain, (![B_147]: (r2_hidden('#skF_2'('#skF_7', B_147), '#skF_5') | r2_hidden('#skF_3'('#skF_7', B_147), B_147) | k2_relat_1('#skF_7')=B_147 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_357])).
% 8.06/2.69  tff(c_376, plain, (![B_147]: (r2_hidden('#skF_2'('#skF_7', B_147), '#skF_5') | r2_hidden('#skF_3'('#skF_7', B_147), B_147) | k2_relat_1('#skF_7')=B_147)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_370])).
% 8.06/2.69  tff(c_58, plain, (![D_68]: (r2_hidden('#skF_8'(D_68), '#skF_5') | ~r2_hidden(D_68, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.06/2.69  tff(c_56, plain, (![D_68]: (k1_funct_1('#skF_7', '#skF_8'(D_68))=D_68 | ~r2_hidden(D_68, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.06/2.69  tff(c_593, plain, (![A_172, B_173, D_174]: (r2_hidden('#skF_2'(A_172, B_173), k1_relat_1(A_172)) | k1_funct_1(A_172, D_174)!='#skF_3'(A_172, B_173) | ~r2_hidden(D_174, k1_relat_1(A_172)) | k2_relat_1(A_172)=B_173 | ~v1_funct_1(A_172) | ~v1_relat_1(A_172))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.06/2.69  tff(c_599, plain, (![B_173, D_68]: (r2_hidden('#skF_2'('#skF_7', B_173), k1_relat_1('#skF_7')) | D_68!='#skF_3'('#skF_7', B_173) | ~r2_hidden('#skF_8'(D_68), k1_relat_1('#skF_7')) | k2_relat_1('#skF_7')=B_173 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(D_68, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_593])).
% 8.06/2.69  tff(c_601, plain, (![B_173, D_68]: (r2_hidden('#skF_2'('#skF_7', B_173), '#skF_5') | D_68!='#skF_3'('#skF_7', B_173) | ~r2_hidden('#skF_8'(D_68), '#skF_5') | k2_relat_1('#skF_7')=B_173 | ~r2_hidden(D_68, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_257, c_257, c_599])).
% 8.06/2.69  tff(c_1225, plain, (![B_249]: (r2_hidden('#skF_2'('#skF_7', B_249), '#skF_5') | ~r2_hidden('#skF_8'('#skF_3'('#skF_7', B_249)), '#skF_5') | k2_relat_1('#skF_7')=B_249 | ~r2_hidden('#skF_3'('#skF_7', B_249), '#skF_6'))), inference(reflexivity, [status(thm), theory('equality')], [c_601])).
% 8.06/2.69  tff(c_1234, plain, (![B_250]: (r2_hidden('#skF_2'('#skF_7', B_250), '#skF_5') | k2_relat_1('#skF_7')=B_250 | ~r2_hidden('#skF_3'('#skF_7', B_250), '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_1225])).
% 8.06/2.69  tff(c_1254, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_5') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_376, c_1234])).
% 8.06/2.69  tff(c_1272, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_107, c_107, c_1254])).
% 8.06/2.69  tff(c_24, plain, (![A_11, B_33]: (k1_funct_1(A_11, '#skF_2'(A_11, B_33))='#skF_1'(A_11, B_33) | r2_hidden('#skF_3'(A_11, B_33), B_33) | k2_relat_1(A_11)=B_33 | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.06/2.69  tff(c_686, plain, (![A_190, B_191, D_192]: (k1_funct_1(A_190, '#skF_2'(A_190, B_191))='#skF_1'(A_190, B_191) | k1_funct_1(A_190, D_192)!='#skF_3'(A_190, B_191) | ~r2_hidden(D_192, k1_relat_1(A_190)) | k2_relat_1(A_190)=B_191 | ~v1_funct_1(A_190) | ~v1_relat_1(A_190))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.06/2.69  tff(c_692, plain, (![B_191, D_68]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_191))='#skF_1'('#skF_7', B_191) | D_68!='#skF_3'('#skF_7', B_191) | ~r2_hidden('#skF_8'(D_68), k1_relat_1('#skF_7')) | k2_relat_1('#skF_7')=B_191 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(D_68, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_686])).
% 8.06/2.69  tff(c_694, plain, (![B_191, D_68]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_191))='#skF_1'('#skF_7', B_191) | D_68!='#skF_3'('#skF_7', B_191) | ~r2_hidden('#skF_8'(D_68), '#skF_5') | k2_relat_1('#skF_7')=B_191 | ~r2_hidden(D_68, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_257, c_692])).
% 8.06/2.69  tff(c_1869, plain, (![B_367]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_367))='#skF_1'('#skF_7', B_367) | ~r2_hidden('#skF_8'('#skF_3'('#skF_7', B_367)), '#skF_5') | k2_relat_1('#skF_7')=B_367 | ~r2_hidden('#skF_3'('#skF_7', B_367), '#skF_6'))), inference(reflexivity, [status(thm), theory('equality')], [c_694])).
% 8.06/2.69  tff(c_1878, plain, (![B_368]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_368))='#skF_1'('#skF_7', B_368) | k2_relat_1('#skF_7')=B_368 | ~r2_hidden('#skF_3'('#skF_7', B_368), '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_1869])).
% 8.06/2.69  tff(c_1916, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_6'))='#skF_1'('#skF_7', '#skF_6') | k2_relat_1('#skF_7')='#skF_6' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_1878])).
% 8.06/2.69  tff(c_1947, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_6'))='#skF_1'('#skF_7', '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_1916])).
% 8.06/2.69  tff(c_1948, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_6'))='#skF_1'('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_107, c_1947])).
% 8.06/2.69  tff(c_150, plain, (![A_100, D_101]: (r2_hidden(k1_funct_1(A_100, D_101), k2_relat_1(A_100)) | ~r2_hidden(D_101, k1_relat_1(A_100)) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.06/2.69  tff(c_4, plain, (![C_5, A_2, B_3]: (r2_hidden(C_5, A_2) | ~r2_hidden(C_5, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.06/2.69  tff(c_630, plain, (![A_183, D_184, A_185]: (r2_hidden(k1_funct_1(A_183, D_184), A_185) | ~m1_subset_1(k2_relat_1(A_183), k1_zfmisc_1(A_185)) | ~r2_hidden(D_184, k1_relat_1(A_183)) | ~v1_funct_1(A_183) | ~v1_relat_1(A_183))), inference(resolution, [status(thm)], [c_150, c_4])).
% 8.06/2.69  tff(c_632, plain, (![D_184]: (r2_hidden(k1_funct_1('#skF_7', D_184), '#skF_6') | ~r2_hidden(D_184, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_149, c_630])).
% 8.06/2.69  tff(c_635, plain, (![D_184]: (r2_hidden(k1_funct_1('#skF_7', D_184), '#skF_6') | ~r2_hidden(D_184, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_257, c_632])).
% 8.06/2.69  tff(c_1971, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1948, c_635])).
% 8.06/2.69  tff(c_1994, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1272, c_1971])).
% 8.06/2.69  tff(c_22, plain, (![A_11, B_33]: (~r2_hidden('#skF_1'(A_11, B_33), B_33) | r2_hidden('#skF_3'(A_11, B_33), B_33) | k2_relat_1(A_11)=B_33 | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.06/2.69  tff(c_158, plain, (![D_68]: (r2_hidden(D_68, k2_relat_1('#skF_7')) | ~r2_hidden('#skF_8'(D_68), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(D_68, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_150])).
% 8.06/2.69  tff(c_162, plain, (![D_68]: (r2_hidden(D_68, k2_relat_1('#skF_7')) | ~r2_hidden('#skF_8'(D_68), k1_relat_1('#skF_7')) | ~r2_hidden(D_68, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_158])).
% 8.06/2.69  tff(c_280, plain, (![D_124]: (r2_hidden(D_124, k2_relat_1('#skF_7')) | ~r2_hidden('#skF_8'(D_124), '#skF_5') | ~r2_hidden(D_124, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_162])).
% 8.06/2.69  tff(c_289, plain, (![D_68]: (r2_hidden(D_68, k2_relat_1('#skF_7')) | ~r2_hidden(D_68, '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_280])).
% 8.06/2.69  tff(c_12, plain, (![A_11, C_47]: (k1_funct_1(A_11, '#skF_4'(A_11, k2_relat_1(A_11), C_47))=C_47 | ~r2_hidden(C_47, k2_relat_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.06/2.69  tff(c_14, plain, (![A_11, C_47]: (r2_hidden('#skF_4'(A_11, k2_relat_1(A_11), C_47), k1_relat_1(A_11)) | ~r2_hidden(C_47, k2_relat_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.06/2.69  tff(c_268, plain, (![C_47]: (r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_47), '#skF_5') | ~r2_hidden(C_47, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_14])).
% 8.06/2.69  tff(c_274, plain, (![C_47]: (r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_47), '#skF_5') | ~r2_hidden(C_47, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_268])).
% 8.06/2.69  tff(c_16, plain, (![A_11, B_33, D_46]: (~r2_hidden('#skF_1'(A_11, B_33), B_33) | k1_funct_1(A_11, D_46)!='#skF_3'(A_11, B_33) | ~r2_hidden(D_46, k1_relat_1(A_11)) | k2_relat_1(A_11)=B_33 | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.06/2.69  tff(c_2005, plain, (![D_46]: (k1_funct_1('#skF_7', D_46)!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(D_46, k1_relat_1('#skF_7')) | k2_relat_1('#skF_7')='#skF_6' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_1994, c_16])).
% 8.06/2.69  tff(c_2020, plain, (![D_46]: (k1_funct_1('#skF_7', D_46)!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(D_46, '#skF_5') | k2_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_257, c_2005])).
% 8.06/2.69  tff(c_2132, plain, (![D_375]: (k1_funct_1('#skF_7', D_375)!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(D_375, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_107, c_2020])).
% 8.06/2.69  tff(c_2520, plain, (![C_395]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_395))!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(C_395, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_274, c_2132])).
% 8.06/2.69  tff(c_2524, plain, (![C_47]: (C_47!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(C_47, k2_relat_1('#skF_7')) | ~r2_hidden(C_47, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2520])).
% 8.06/2.69  tff(c_2528, plain, (![C_396]: (C_396!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(C_396, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_2524])).
% 8.06/2.69  tff(c_2673, plain, (![D_397]: (D_397!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(D_397, '#skF_6'))), inference(resolution, [status(thm)], [c_289, c_2528])).
% 8.06/2.69  tff(c_3639, plain, (![A_467]: ('#skF_3'(A_467, '#skF_6')!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden('#skF_1'(A_467, '#skF_6'), '#skF_6') | k2_relat_1(A_467)='#skF_6' | ~v1_funct_1(A_467) | ~v1_relat_1(A_467))), inference(resolution, [status(thm)], [c_22, c_2673])).
% 8.06/2.69  tff(c_3654, plain, (k2_relat_1('#skF_7')='#skF_6' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_1994, c_3639])).
% 8.06/2.69  tff(c_3669, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_3654])).
% 8.06/2.69  tff(c_3671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_3669])).
% 8.06/2.69  tff(c_3672, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_256])).
% 8.06/2.69  tff(c_38, plain, (![C_64, A_62]: (k1_xboole_0=C_64 | ~v1_funct_2(C_64, A_62, k1_xboole_0) | k1_xboole_0=A_62 | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.06/2.69  tff(c_3704, plain, (![C_473, A_474]: (C_473='#skF_6' | ~v1_funct_2(C_473, A_474, '#skF_6') | A_474='#skF_6' | ~m1_subset_1(C_473, k1_zfmisc_1(k2_zfmisc_1(A_474, '#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_3672, c_3672, c_3672, c_3672, c_38])).
% 8.06/2.69  tff(c_3711, plain, ('#skF_7'='#skF_6' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_50, c_3704])).
% 8.06/2.69  tff(c_3715, plain, ('#skF_7'='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3711])).
% 8.06/2.69  tff(c_3716, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_3715])).
% 8.06/2.69  tff(c_3673, plain, (k1_relat_1('#skF_7')!='#skF_5'), inference(splitRight, [status(thm)], [c_256])).
% 8.06/2.69  tff(c_3718, plain, (k1_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3716, c_3673])).
% 8.06/2.69  tff(c_3730, plain, (v1_funct_2('#skF_7', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3716, c_52])).
% 8.06/2.69  tff(c_3722, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3716, c_121])).
% 8.06/2.69  tff(c_3729, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_3716, c_50])).
% 8.06/2.69  tff(c_44, plain, (![B_63, C_64]: (k1_relset_1(k1_xboole_0, B_63, C_64)=k1_xboole_0 | ~v1_funct_2(C_64, k1_xboole_0, B_63) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_63))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.06/2.69  tff(c_3825, plain, (![B_482, C_483]: (k1_relset_1('#skF_6', B_482, C_483)='#skF_6' | ~v1_funct_2(C_483, '#skF_6', B_482) | ~m1_subset_1(C_483, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_482))))), inference(demodulation, [status(thm), theory('equality')], [c_3672, c_3672, c_3672, c_3672, c_44])).
% 8.06/2.69  tff(c_3828, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_7')='#skF_6' | ~v1_funct_2('#skF_7', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_3729, c_3825])).
% 8.06/2.69  tff(c_3835, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3730, c_3722, c_3828])).
% 8.06/2.69  tff(c_3837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3718, c_3835])).
% 8.06/2.69  tff(c_3838, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_3715])).
% 8.06/2.69  tff(c_3850, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3838, c_83])).
% 8.06/2.69  tff(c_3856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_3850])).
% 8.06/2.69  tff(c_3858, plain, (v1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_169])).
% 8.06/2.69  tff(c_3958, plain, (![B_512, A_513, C_514]: (k1_xboole_0=B_512 | k1_relset_1(A_513, B_512, C_514)=A_513 | ~v1_funct_2(C_514, A_513, B_512) | ~m1_subset_1(C_514, k1_zfmisc_1(k2_zfmisc_1(A_513, B_512))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.06/2.69  tff(c_3965, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_3958])).
% 8.06/2.69  tff(c_3969, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_121, c_3965])).
% 8.06/2.69  tff(c_3970, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_3969])).
% 8.06/2.69  tff(c_4003, plain, (![A_516, B_517]: (r2_hidden('#skF_2'(A_516, B_517), k1_relat_1(A_516)) | r2_hidden('#skF_3'(A_516, B_517), B_517) | k2_relat_1(A_516)=B_517 | ~v1_funct_1(A_516) | ~v1_relat_1(A_516))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.06/2.69  tff(c_4016, plain, (![B_517]: (r2_hidden('#skF_2'('#skF_7', B_517), '#skF_5') | r2_hidden('#skF_3'('#skF_7', B_517), B_517) | k2_relat_1('#skF_7')=B_517 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3970, c_4003])).
% 8.06/2.69  tff(c_4022, plain, (![B_517]: (r2_hidden('#skF_2'('#skF_7', B_517), '#skF_5') | r2_hidden('#skF_3'('#skF_7', B_517), B_517) | k2_relat_1('#skF_7')=B_517)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_4016])).
% 8.06/2.69  tff(c_4306, plain, (![A_551, B_552, D_553]: (r2_hidden('#skF_2'(A_551, B_552), k1_relat_1(A_551)) | k1_funct_1(A_551, D_553)!='#skF_3'(A_551, B_552) | ~r2_hidden(D_553, k1_relat_1(A_551)) | k2_relat_1(A_551)=B_552 | ~v1_funct_1(A_551) | ~v1_relat_1(A_551))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.06/2.69  tff(c_4312, plain, (![B_552, D_68]: (r2_hidden('#skF_2'('#skF_7', B_552), k1_relat_1('#skF_7')) | D_68!='#skF_3'('#skF_7', B_552) | ~r2_hidden('#skF_8'(D_68), k1_relat_1('#skF_7')) | k2_relat_1('#skF_7')=B_552 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(D_68, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_4306])).
% 8.06/2.69  tff(c_4314, plain, (![B_552, D_68]: (r2_hidden('#skF_2'('#skF_7', B_552), '#skF_5') | D_68!='#skF_3'('#skF_7', B_552) | ~r2_hidden('#skF_8'(D_68), '#skF_5') | k2_relat_1('#skF_7')=B_552 | ~r2_hidden(D_68, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_3970, c_3970, c_4312])).
% 8.06/2.69  tff(c_4939, plain, (![B_635]: (r2_hidden('#skF_2'('#skF_7', B_635), '#skF_5') | ~r2_hidden('#skF_8'('#skF_3'('#skF_7', B_635)), '#skF_5') | k2_relat_1('#skF_7')=B_635 | ~r2_hidden('#skF_3'('#skF_7', B_635), '#skF_6'))), inference(reflexivity, [status(thm), theory('equality')], [c_4314])).
% 8.06/2.69  tff(c_4948, plain, (![B_636]: (r2_hidden('#skF_2'('#skF_7', B_636), '#skF_5') | k2_relat_1('#skF_7')=B_636 | ~r2_hidden('#skF_3'('#skF_7', B_636), '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_4939])).
% 8.06/2.69  tff(c_4972, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_5') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_4022, c_4948])).
% 8.06/2.69  tff(c_4994, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_107, c_107, c_4972])).
% 8.06/2.69  tff(c_4381, plain, (![A_569, B_570, D_571]: (k1_funct_1(A_569, '#skF_2'(A_569, B_570))='#skF_1'(A_569, B_570) | k1_funct_1(A_569, D_571)!='#skF_3'(A_569, B_570) | ~r2_hidden(D_571, k1_relat_1(A_569)) | k2_relat_1(A_569)=B_570 | ~v1_funct_1(A_569) | ~v1_relat_1(A_569))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.06/2.69  tff(c_4387, plain, (![B_570, D_68]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_570))='#skF_1'('#skF_7', B_570) | D_68!='#skF_3'('#skF_7', B_570) | ~r2_hidden('#skF_8'(D_68), k1_relat_1('#skF_7')) | k2_relat_1('#skF_7')=B_570 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(D_68, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_4381])).
% 8.06/2.69  tff(c_4389, plain, (![B_570, D_68]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_570))='#skF_1'('#skF_7', B_570) | D_68!='#skF_3'('#skF_7', B_570) | ~r2_hidden('#skF_8'(D_68), '#skF_5') | k2_relat_1('#skF_7')=B_570 | ~r2_hidden(D_68, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_3970, c_4387])).
% 8.06/2.69  tff(c_5237, plain, (![B_681]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_681))='#skF_1'('#skF_7', B_681) | ~r2_hidden('#skF_8'('#skF_3'('#skF_7', B_681)), '#skF_5') | k2_relat_1('#skF_7')=B_681 | ~r2_hidden('#skF_3'('#skF_7', B_681), '#skF_6'))), inference(reflexivity, [status(thm), theory('equality')], [c_4389])).
% 8.06/2.69  tff(c_5246, plain, (![B_682]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_682))='#skF_1'('#skF_7', B_682) | k2_relat_1('#skF_7')=B_682 | ~r2_hidden('#skF_3'('#skF_7', B_682), '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_5237])).
% 8.06/2.69  tff(c_5272, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_6'))='#skF_1'('#skF_7', '#skF_6') | k2_relat_1('#skF_7')='#skF_6' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_24, c_5246])).
% 8.06/2.69  tff(c_5295, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_6'))='#skF_1'('#skF_7', '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_5272])).
% 8.06/2.69  tff(c_5296, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_6'))='#skF_1'('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_107, c_5295])).
% 8.06/2.69  tff(c_4414, plain, (![A_578, D_579, A_580]: (r2_hidden(k1_funct_1(A_578, D_579), A_580) | ~m1_subset_1(k2_relat_1(A_578), k1_zfmisc_1(A_580)) | ~r2_hidden(D_579, k1_relat_1(A_578)) | ~v1_funct_1(A_578) | ~v1_relat_1(A_578))), inference(resolution, [status(thm)], [c_150, c_4])).
% 8.06/2.69  tff(c_4416, plain, (![D_579]: (r2_hidden(k1_funct_1('#skF_7', D_579), '#skF_6') | ~r2_hidden(D_579, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_149, c_4414])).
% 8.06/2.69  tff(c_4419, plain, (![D_579]: (r2_hidden(k1_funct_1('#skF_7', D_579), '#skF_6') | ~r2_hidden(D_579, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_3970, c_4416])).
% 8.06/2.69  tff(c_5316, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5296, c_4419])).
% 8.06/2.69  tff(c_5338, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4994, c_5316])).
% 8.06/2.69  tff(c_3993, plain, (![D_515]: (r2_hidden(D_515, k2_relat_1('#skF_7')) | ~r2_hidden('#skF_8'(D_515), '#skF_5') | ~r2_hidden(D_515, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3970, c_162])).
% 8.06/2.69  tff(c_4002, plain, (![D_68]: (r2_hidden(D_68, k2_relat_1('#skF_7')) | ~r2_hidden(D_68, '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_3993])).
% 8.06/2.69  tff(c_3981, plain, (![C_47]: (r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_47), '#skF_5') | ~r2_hidden(C_47, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3970, c_14])).
% 8.06/2.69  tff(c_3987, plain, (![C_47]: (r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_47), '#skF_5') | ~r2_hidden(C_47, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_3981])).
% 8.06/2.69  tff(c_5354, plain, (![D_46]: (k1_funct_1('#skF_7', D_46)!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(D_46, k1_relat_1('#skF_7')) | k2_relat_1('#skF_7')='#skF_6' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_5338, c_16])).
% 8.06/2.69  tff(c_5370, plain, (![D_46]: (k1_funct_1('#skF_7', D_46)!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(D_46, '#skF_5') | k2_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_3970, c_5354])).
% 8.06/2.69  tff(c_5516, plain, (![D_687]: (k1_funct_1('#skF_7', D_687)!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(D_687, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_107, c_5370])).
% 8.06/2.69  tff(c_5875, plain, (![C_710]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_710))!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(C_710, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_3987, c_5516])).
% 8.06/2.69  tff(c_5879, plain, (![C_47]: (C_47!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(C_47, k2_relat_1('#skF_7')) | ~r2_hidden(C_47, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_5875])).
% 8.06/2.69  tff(c_5883, plain, (![C_711]: (C_711!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(C_711, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_5879])).
% 8.06/2.69  tff(c_6018, plain, (![D_712]: (D_712!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(D_712, '#skF_6'))), inference(resolution, [status(thm)], [c_4002, c_5883])).
% 8.06/2.69  tff(c_6919, plain, (![A_783]: ('#skF_3'(A_783, '#skF_6')!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden('#skF_1'(A_783, '#skF_6'), '#skF_6') | k2_relat_1(A_783)='#skF_6' | ~v1_funct_1(A_783) | ~v1_relat_1(A_783))), inference(resolution, [status(thm)], [c_22, c_6018])).
% 8.06/2.69  tff(c_6934, plain, (k2_relat_1('#skF_7')='#skF_6' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_5338, c_6919])).
% 8.06/2.69  tff(c_6949, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_54, c_6934])).
% 8.06/2.69  tff(c_6951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_6949])).
% 8.06/2.69  tff(c_6952, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_3969])).
% 8.06/2.69  tff(c_6973, plain, (![C_786, A_787]: (C_786='#skF_6' | ~v1_funct_2(C_786, A_787, '#skF_6') | A_787='#skF_6' | ~m1_subset_1(C_786, k1_zfmisc_1(k2_zfmisc_1(A_787, '#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_6952, c_6952, c_6952, c_6952, c_38])).
% 8.06/2.69  tff(c_6980, plain, ('#skF_7'='#skF_6' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_50, c_6973])).
% 8.06/2.69  tff(c_6984, plain, ('#skF_7'='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6980])).
% 8.06/2.69  tff(c_6985, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_6984])).
% 8.06/2.69  tff(c_6953, plain, (k1_relat_1('#skF_7')!='#skF_5'), inference(splitRight, [status(thm)], [c_3969])).
% 8.06/2.69  tff(c_6987, plain, (k1_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6985, c_6953])).
% 8.06/2.69  tff(c_7000, plain, (v1_funct_2('#skF_7', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6985, c_52])).
% 8.06/2.69  tff(c_6992, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6985, c_121])).
% 8.06/2.69  tff(c_6999, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_6985, c_50])).
% 8.06/2.69  tff(c_7102, plain, (![B_793, C_794]: (k1_relset_1('#skF_6', B_793, C_794)='#skF_6' | ~v1_funct_2(C_794, '#skF_6', B_793) | ~m1_subset_1(C_794, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_793))))), inference(demodulation, [status(thm), theory('equality')], [c_6952, c_6952, c_6952, c_6952, c_44])).
% 8.06/2.69  tff(c_7105, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_7')='#skF_6' | ~v1_funct_2('#skF_7', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_6999, c_7102])).
% 8.06/2.69  tff(c_7112, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7000, c_6992, c_7105])).
% 8.06/2.69  tff(c_7114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6987, c_7112])).
% 8.06/2.69  tff(c_7115, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_6984])).
% 8.06/2.69  tff(c_7132, plain, (v1_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7115, c_54])).
% 8.06/2.69  tff(c_26, plain, (![A_11, B_33]: (r2_hidden('#skF_2'(A_11, B_33), k1_relat_1(A_11)) | r2_hidden('#skF_3'(A_11, B_33), B_33) | k2_relat_1(A_11)=B_33 | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.06/2.69  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.06/2.69  tff(c_6961, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_6952, c_2])).
% 8.06/2.69  tff(c_7124, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7115, c_149])).
% 8.06/2.69  tff(c_7317, plain, (![A_822, D_823, A_824]: (r2_hidden(k1_funct_1(A_822, D_823), A_824) | ~m1_subset_1(k2_relat_1(A_822), k1_zfmisc_1(A_824)) | ~r2_hidden(D_823, k1_relat_1(A_822)) | ~v1_funct_1(A_822) | ~v1_relat_1(A_822))), inference(resolution, [status(thm)], [c_150, c_4])).
% 8.06/2.69  tff(c_7319, plain, (![D_823]: (r2_hidden(k1_funct_1('#skF_6', D_823), '#skF_6') | ~r2_hidden(D_823, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_7124, c_7317])).
% 8.06/2.69  tff(c_7323, plain, (![D_825]: (r2_hidden(k1_funct_1('#skF_6', D_825), '#skF_6') | ~r2_hidden(D_825, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_3858, c_7132, c_7319])).
% 8.06/2.69  tff(c_28, plain, (![B_52, A_51]: (~r1_tarski(B_52, A_51) | ~r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.06/2.69  tff(c_7328, plain, (![D_825]: (~r1_tarski('#skF_6', k1_funct_1('#skF_6', D_825)) | ~r2_hidden(D_825, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_7323, c_28])).
% 8.06/2.69  tff(c_7353, plain, (![D_829]: (~r2_hidden(D_829, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_6961, c_7328])).
% 8.06/2.69  tff(c_7361, plain, (![B_33]: (r2_hidden('#skF_3'('#skF_6', B_33), B_33) | k2_relat_1('#skF_6')=B_33 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_26, c_7353])).
% 8.06/2.69  tff(c_7416, plain, (![B_831]: (r2_hidden('#skF_3'('#skF_6', B_831), B_831) | k2_relat_1('#skF_6')=B_831)), inference(demodulation, [status(thm), theory('equality')], [c_3858, c_7132, c_7361])).
% 8.06/2.69  tff(c_7341, plain, (![D_825]: (~r2_hidden(D_825, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_6961, c_7328])).
% 8.06/2.69  tff(c_7432, plain, (k2_relat_1('#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_7416, c_7341])).
% 8.06/2.69  tff(c_7126, plain, (k2_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7115, c_107])).
% 8.06/2.69  tff(c_7442, plain, (k1_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7432, c_7126])).
% 8.06/2.69  tff(c_7434, plain, (![B_831]: (~r1_tarski(B_831, '#skF_3'('#skF_6', B_831)) | k2_relat_1('#skF_6')=B_831)), inference(resolution, [status(thm)], [c_7416, c_28])).
% 8.06/2.69  tff(c_7506, plain, (![B_834]: (~r1_tarski(B_834, '#skF_3'('#skF_6', B_834)) | k1_relat_1('#skF_6')=B_834)), inference(demodulation, [status(thm), theory('equality')], [c_7432, c_7434])).
% 8.06/2.69  tff(c_7510, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_6961, c_7506])).
% 8.06/2.69  tff(c_7514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7442, c_7510])).
% 8.06/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.06/2.69  
% 8.06/2.69  Inference rules
% 8.06/2.69  ----------------------
% 8.06/2.69  #Ref     : 8
% 8.06/2.69  #Sup     : 1460
% 8.06/2.69  #Fact    : 0
% 8.06/2.69  #Define  : 0
% 8.06/2.69  #Split   : 29
% 8.06/2.69  #Chain   : 0
% 8.06/2.69  #Close   : 0
% 8.06/2.69  
% 8.06/2.69  Ordering : KBO
% 8.06/2.69  
% 8.06/2.69  Simplification rules
% 8.06/2.69  ----------------------
% 8.06/2.69  #Subsume      : 525
% 8.06/2.69  #Demod        : 847
% 8.06/2.69  #Tautology    : 233
% 8.06/2.69  #SimpNegUnit  : 164
% 8.06/2.69  #BackRed      : 117
% 8.06/2.69  
% 8.06/2.69  #Partial instantiations: 0
% 8.06/2.69  #Strategies tried      : 1
% 8.06/2.69  
% 8.06/2.69  Timing (in seconds)
% 8.06/2.69  ----------------------
% 8.24/2.70  Preprocessing        : 0.33
% 8.24/2.70  Parsing              : 0.17
% 8.24/2.70  CNF conversion       : 0.03
% 8.24/2.70  Main loop            : 1.57
% 8.24/2.70  Inferencing          : 0.56
% 8.24/2.70  Reduction            : 0.45
% 8.24/2.70  Demodulation         : 0.28
% 8.24/2.70  BG Simplification    : 0.05
% 8.24/2.70  Subsumption          : 0.38
% 8.24/2.70  Abstraction          : 0.07
% 8.24/2.70  MUC search           : 0.00
% 8.24/2.70  Cooper               : 0.00
% 8.24/2.70  Total                : 1.96
% 8.24/2.70  Index Insertion      : 0.00
% 8.24/2.70  Index Deletion       : 0.00
% 8.24/2.70  Index Matching       : 0.00
% 8.24/2.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
