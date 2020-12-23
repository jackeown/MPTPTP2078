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
% DateTime   : Thu Dec  3 10:11:03 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 123 expanded)
%              Number of leaves         :   45 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :  121 ( 235 expanded)
%              Number of equality atoms :   34 (  51 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_134,axiom,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_116,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_47,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_45,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_304,plain,(
    ! [C_104,B_105,A_106] :
      ( v5_relat_1(C_104,B_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_318,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_304])).

tff(c_60,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_30,plain,(
    ! [A_28,B_29] : v1_relat_1(k2_zfmisc_1(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_177,plain,(
    ! [B_88,A_89] :
      ( v1_relat_1(B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_89))
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_186,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_62,c_177])).

tff(c_191,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_186])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_64,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_488,plain,(
    ! [A_141,B_142,C_143] :
      ( k1_relset_1(A_141,B_142,C_143) = k1_relat_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_502,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_488])).

tff(c_1490,plain,(
    ! [B_178,A_179,C_180] :
      ( k1_xboole_0 = B_178
      | k1_relset_1(A_179,B_178,C_180) = A_179
      | ~ v1_funct_2(C_180,A_179,B_178)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_179,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1501,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1490])).

tff(c_1506,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_502,c_1501])).

tff(c_1507,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1506])).

tff(c_32,plain,(
    ! [C_32,B_31,A_30] :
      ( m1_subset_1(k1_funct_1(C_32,B_31),A_30)
      | ~ r2_hidden(B_31,k1_relat_1(C_32))
      | ~ v1_funct_1(C_32)
      | ~ v5_relat_1(C_32,A_30)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1511,plain,(
    ! [B_31,A_30] :
      ( m1_subset_1(k1_funct_1('#skF_5',B_31),A_30)
      | ~ r2_hidden(B_31,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_30)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1507,c_32])).

tff(c_1597,plain,(
    ! [B_182,A_183] :
      ( m1_subset_1(k1_funct_1('#skF_5',B_182),A_183)
      | ~ r2_hidden(B_182,'#skF_2')
      | ~ v5_relat_1('#skF_5',A_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_66,c_1511])).

tff(c_171,plain,(
    ! [A_86,B_87] :
      ( r2_hidden(A_86,B_87)
      | v1_xboole_0(B_87)
      | ~ m1_subset_1(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_56,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_175,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_171,c_56])).

tff(c_176,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_1635,plain,
    ( ~ r2_hidden('#skF_4','#skF_2')
    | ~ v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_1597,c_176])).

tff(c_1648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_60,c_1635])).

tff(c_1649,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_42,plain,(
    ! [A_39] :
      ( r2_hidden('#skF_1'(A_39),A_39)
      | k1_xboole_0 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_18,plain,(
    ! [A_16,B_17] : k6_subset_1(A_16,B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_14,B_15] : m1_subset_1(k6_subset_1(A_14,B_15),k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_67,plain,(
    ! [A_14,B_15] : m1_subset_1(k4_xboole_0(A_14,B_15),k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16])).

tff(c_1925,plain,(
    ! [C_226,B_227,A_228] :
      ( ~ v1_xboole_0(C_226)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(C_226))
      | ~ r2_hidden(A_228,B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1935,plain,(
    ! [A_229,A_230,B_231] :
      ( ~ v1_xboole_0(A_229)
      | ~ r2_hidden(A_230,k4_xboole_0(A_229,B_231)) ) ),
    inference(resolution,[status(thm)],[c_67,c_1925])).

tff(c_1949,plain,(
    ! [A_232,B_233] :
      ( ~ v1_xboole_0(A_232)
      | k4_xboole_0(A_232,B_233) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_1935])).

tff(c_1952,plain,(
    ! [B_233] : k4_xboole_0('#skF_3',B_233) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1649,c_1949])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1953,plain,(
    ! [B_234] : k4_xboole_0('#skF_3',B_234) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1649,c_1949])).

tff(c_2014,plain,(
    ! [B_239] : k3_xboole_0('#skF_3',B_239) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1953])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2022,plain,(
    ! [B_239] : k5_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3',B_239) ),
    inference(superposition,[status(thm),theory(equality)],[c_2014,c_4])).

tff(c_2029,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_12,c_2022])).

tff(c_2031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2029])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:02:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.61  
% 3.82/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.82/1.62  
% 3.82/1.62  %Foreground sorts:
% 3.82/1.62  
% 3.82/1.62  
% 3.82/1.62  %Background operators:
% 3.82/1.62  
% 3.82/1.62  
% 3.82/1.62  %Foreground operators:
% 3.82/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.82/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.82/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.82/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.82/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.82/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.82/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.82/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.82/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.82/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.82/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.82/1.62  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.82/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.82/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.82/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.82/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.82/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.82/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.82/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.82/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.82/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.82/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.82/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.82/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.82/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.82/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.82/1.62  
% 3.82/1.63  tff(f_147, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.82/1.63  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.82/1.63  tff(f_75, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.82/1.63  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.82/1.63  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.82/1.63  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.82/1.63  tff(f_85, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 3.82/1.63  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.82/1.63  tff(f_116, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 3.82/1.63  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.82/1.63  tff(f_45, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 3.82/1.63  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.82/1.63  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.82/1.63  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.82/1.63  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.82/1.63  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.82/1.63  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.82/1.63  tff(c_304, plain, (![C_104, B_105, A_106]: (v5_relat_1(C_104, B_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.82/1.63  tff(c_318, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_304])).
% 3.82/1.63  tff(c_60, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.82/1.63  tff(c_30, plain, (![A_28, B_29]: (v1_relat_1(k2_zfmisc_1(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.82/1.63  tff(c_177, plain, (![B_88, A_89]: (v1_relat_1(B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_89)) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.82/1.63  tff(c_186, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_62, c_177])).
% 3.82/1.63  tff(c_191, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_186])).
% 3.82/1.63  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.82/1.63  tff(c_64, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.82/1.63  tff(c_488, plain, (![A_141, B_142, C_143]: (k1_relset_1(A_141, B_142, C_143)=k1_relat_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.82/1.63  tff(c_502, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_488])).
% 3.82/1.63  tff(c_1490, plain, (![B_178, A_179, C_180]: (k1_xboole_0=B_178 | k1_relset_1(A_179, B_178, C_180)=A_179 | ~v1_funct_2(C_180, A_179, B_178) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_179, B_178))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.82/1.63  tff(c_1501, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_1490])).
% 3.82/1.63  tff(c_1506, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_502, c_1501])).
% 3.82/1.63  tff(c_1507, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_58, c_1506])).
% 3.82/1.63  tff(c_32, plain, (![C_32, B_31, A_30]: (m1_subset_1(k1_funct_1(C_32, B_31), A_30) | ~r2_hidden(B_31, k1_relat_1(C_32)) | ~v1_funct_1(C_32) | ~v5_relat_1(C_32, A_30) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.82/1.63  tff(c_1511, plain, (![B_31, A_30]: (m1_subset_1(k1_funct_1('#skF_5', B_31), A_30) | ~r2_hidden(B_31, '#skF_2') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_30) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1507, c_32])).
% 3.82/1.63  tff(c_1597, plain, (![B_182, A_183]: (m1_subset_1(k1_funct_1('#skF_5', B_182), A_183) | ~r2_hidden(B_182, '#skF_2') | ~v5_relat_1('#skF_5', A_183))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_66, c_1511])).
% 3.82/1.63  tff(c_171, plain, (![A_86, B_87]: (r2_hidden(A_86, B_87) | v1_xboole_0(B_87) | ~m1_subset_1(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.82/1.63  tff(c_56, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.82/1.63  tff(c_175, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_171, c_56])).
% 3.82/1.63  tff(c_176, plain, (~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_175])).
% 3.82/1.63  tff(c_1635, plain, (~r2_hidden('#skF_4', '#skF_2') | ~v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_1597, c_176])).
% 3.82/1.63  tff(c_1648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_318, c_60, c_1635])).
% 3.82/1.63  tff(c_1649, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_175])).
% 3.82/1.63  tff(c_42, plain, (![A_39]: (r2_hidden('#skF_1'(A_39), A_39) | k1_xboole_0=A_39)), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.82/1.63  tff(c_18, plain, (![A_16, B_17]: (k6_subset_1(A_16, B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.82/1.63  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(k6_subset_1(A_14, B_15), k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.82/1.63  tff(c_67, plain, (![A_14, B_15]: (m1_subset_1(k4_xboole_0(A_14, B_15), k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16])).
% 3.82/1.63  tff(c_1925, plain, (![C_226, B_227, A_228]: (~v1_xboole_0(C_226) | ~m1_subset_1(B_227, k1_zfmisc_1(C_226)) | ~r2_hidden(A_228, B_227))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.82/1.63  tff(c_1935, plain, (![A_229, A_230, B_231]: (~v1_xboole_0(A_229) | ~r2_hidden(A_230, k4_xboole_0(A_229, B_231)))), inference(resolution, [status(thm)], [c_67, c_1925])).
% 3.82/1.63  tff(c_1949, plain, (![A_232, B_233]: (~v1_xboole_0(A_232) | k4_xboole_0(A_232, B_233)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_1935])).
% 3.82/1.63  tff(c_1952, plain, (![B_233]: (k4_xboole_0('#skF_3', B_233)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1649, c_1949])).
% 3.82/1.63  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.82/1.63  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.82/1.63  tff(c_1953, plain, (![B_234]: (k4_xboole_0('#skF_3', B_234)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1649, c_1949])).
% 3.82/1.63  tff(c_2014, plain, (![B_239]: (k3_xboole_0('#skF_3', B_239)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_1953])).
% 3.82/1.63  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.82/1.63  tff(c_2022, plain, (![B_239]: (k5_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', B_239))), inference(superposition, [status(thm), theory('equality')], [c_2014, c_4])).
% 3.82/1.63  tff(c_2029, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_12, c_2022])).
% 3.82/1.63  tff(c_2031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2029])).
% 3.82/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.63  
% 3.82/1.63  Inference rules
% 3.82/1.63  ----------------------
% 3.82/1.63  #Ref     : 0
% 3.82/1.63  #Sup     : 468
% 3.82/1.63  #Fact    : 0
% 3.82/1.63  #Define  : 0
% 3.82/1.63  #Split   : 3
% 3.82/1.63  #Chain   : 0
% 3.82/1.63  #Close   : 0
% 3.82/1.63  
% 3.82/1.63  Ordering : KBO
% 3.82/1.63  
% 3.82/1.63  Simplification rules
% 3.82/1.63  ----------------------
% 3.82/1.63  #Subsume      : 62
% 3.82/1.63  #Demod        : 357
% 3.82/1.63  #Tautology    : 241
% 3.82/1.63  #SimpNegUnit  : 2
% 3.82/1.63  #BackRed      : 1
% 3.82/1.63  
% 3.82/1.63  #Partial instantiations: 0
% 3.82/1.63  #Strategies tried      : 1
% 3.82/1.63  
% 3.82/1.63  Timing (in seconds)
% 3.82/1.63  ----------------------
% 3.82/1.63  Preprocessing        : 0.35
% 3.82/1.63  Parsing              : 0.18
% 3.82/1.63  CNF conversion       : 0.02
% 3.82/1.63  Main loop            : 0.51
% 3.82/1.63  Inferencing          : 0.16
% 3.82/1.63  Reduction            : 0.22
% 3.82/1.63  Demodulation         : 0.17
% 3.82/1.63  BG Simplification    : 0.03
% 3.82/1.63  Subsumption          : 0.07
% 3.82/1.63  Abstraction          : 0.03
% 3.82/1.63  MUC search           : 0.00
% 3.82/1.63  Cooper               : 0.00
% 3.82/1.63  Total                : 0.89
% 3.82/1.63  Index Insertion      : 0.00
% 3.82/1.63  Index Deletion       : 0.00
% 3.82/1.63  Index Matching       : 0.00
% 3.82/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
