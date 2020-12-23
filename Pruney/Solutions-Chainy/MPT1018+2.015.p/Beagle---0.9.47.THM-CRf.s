%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:47 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 284 expanded)
%              Number of leaves         :   27 ( 114 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 934 expanded)
%              Number of equality atoms :   47 ( 349 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_68,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_28,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_51,plain,(
    ! [A_20,B_21,C_22] :
      ( k1_relset_1(A_20,B_21,C_22) = k1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_51])).

tff(c_186,plain,(
    ! [B_50,A_51,C_52] :
      ( k1_xboole_0 = B_50
      | k1_relset_1(A_51,B_50,C_52) = A_51
      | ~ v1_funct_2(C_52,A_51,B_50)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_189,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_186])).

tff(c_192,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_55,c_189])).

tff(c_193,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_24,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    ! [B_18,A_19] :
      ( v1_relat_1(B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_19))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_44])).

tff(c_50,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_47])).

tff(c_38,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_97,plain,(
    ! [B_34,A_35,C_36] :
      ( k1_xboole_0 = B_34
      | k1_relset_1(A_35,B_34,C_36) = A_35
      | ~ v1_funct_2(C_36,A_35,B_34)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_35,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_100,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_97])).

tff(c_103,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_55,c_100])).

tff(c_104,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_26,plain,(
    k1_funct_1('#skF_2','#skF_3') = k1_funct_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_64,plain,(
    ! [B_30,A_31] :
      ( k1_funct_1(k2_funct_1(B_30),k1_funct_1(B_30,A_31)) = A_31
      | ~ r2_hidden(A_31,k1_relat_1(B_30))
      | ~ v2_funct_1(B_30)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_79,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_64])).

tff(c_83,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38,c_32,c_79])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_105,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_84])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_105])).

tff(c_111,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_110,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_20,plain,(
    ! [B_12,C_13] :
      ( k1_relset_1(k1_xboole_0,B_12,C_13) = k1_xboole_0
      | ~ v1_funct_2(C_13,k1_xboole_0,B_12)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_138,plain,(
    ! [B_43,C_44] :
      ( k1_relset_1('#skF_1',B_43,C_44) = '#skF_1'
      | ~ v1_funct_2(C_44,'#skF_1',B_43)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_43))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_110,c_110,c_110,c_20])).

tff(c_141,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_138])).

tff(c_144,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_55,c_141])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_144])).

tff(c_147,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k1_funct_1(k2_funct_1(B_7),k1_funct_1(B_7,A_6)) = A_6
      | ~ r2_hidden(A_6,k1_relat_1(B_7))
      | ~ v2_funct_1(B_7)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_155,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_8])).

tff(c_162,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38,c_32,c_155])).

tff(c_163,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_162])).

tff(c_194,plain,(
    ~ r2_hidden('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_163])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_194])).

tff(c_201,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_200,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_221,plain,(
    ! [B_56,C_57] :
      ( k1_relset_1('#skF_1',B_56,C_57) = '#skF_1'
      | ~ v1_funct_2(C_57,'#skF_1',B_56)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_56))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_200,c_200,c_20])).

tff(c_224,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_221])).

tff(c_227,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_55,c_224])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:47:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.26  
% 2.17/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.26  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.26  
% 2.17/1.26  %Foreground sorts:
% 2.17/1.26  
% 2.17/1.26  
% 2.17/1.26  %Background operators:
% 2.17/1.26  
% 2.17/1.26  
% 2.17/1.26  %Foreground operators:
% 2.17/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.26  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.17/1.26  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.26  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.17/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.17/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.17/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.26  
% 2.17/1.28  tff(f_86, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 2.17/1.28  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.17/1.28  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.17/1.28  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.17/1.28  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.17/1.28  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 2.17/1.28  tff(c_28, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.17/1.28  tff(c_36, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.17/1.28  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.17/1.28  tff(c_51, plain, (![A_20, B_21, C_22]: (k1_relset_1(A_20, B_21, C_22)=k1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.17/1.28  tff(c_55, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_51])).
% 2.17/1.28  tff(c_186, plain, (![B_50, A_51, C_52]: (k1_xboole_0=B_50 | k1_relset_1(A_51, B_50, C_52)=A_51 | ~v1_funct_2(C_52, A_51, B_50) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.17/1.28  tff(c_189, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_186])).
% 2.17/1.28  tff(c_192, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_55, c_189])).
% 2.17/1.28  tff(c_193, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_192])).
% 2.17/1.28  tff(c_24, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.17/1.28  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.17/1.28  tff(c_44, plain, (![B_18, A_19]: (v1_relat_1(B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_19)) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.28  tff(c_47, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_44])).
% 2.17/1.28  tff(c_50, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_47])).
% 2.17/1.28  tff(c_38, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.17/1.28  tff(c_32, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.17/1.28  tff(c_30, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.17/1.28  tff(c_97, plain, (![B_34, A_35, C_36]: (k1_xboole_0=B_34 | k1_relset_1(A_35, B_34, C_36)=A_35 | ~v1_funct_2(C_36, A_35, B_34) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_35, B_34))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.17/1.28  tff(c_100, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_97])).
% 2.17/1.28  tff(c_103, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_55, c_100])).
% 2.17/1.28  tff(c_104, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_103])).
% 2.17/1.28  tff(c_26, plain, (k1_funct_1('#skF_2', '#skF_3')=k1_funct_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.17/1.28  tff(c_64, plain, (![B_30, A_31]: (k1_funct_1(k2_funct_1(B_30), k1_funct_1(B_30, A_31))=A_31 | ~r2_hidden(A_31, k1_relat_1(B_30)) | ~v2_funct_1(B_30) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.28  tff(c_79, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | ~r2_hidden('#skF_3', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_64])).
% 2.17/1.28  tff(c_83, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | ~r2_hidden('#skF_3', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38, c_32, c_79])).
% 2.17/1.28  tff(c_84, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_83])).
% 2.17/1.28  tff(c_105, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_84])).
% 2.17/1.28  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_105])).
% 2.17/1.28  tff(c_111, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(splitRight, [status(thm)], [c_103])).
% 2.17/1.28  tff(c_110, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_103])).
% 2.17/1.28  tff(c_20, plain, (![B_12, C_13]: (k1_relset_1(k1_xboole_0, B_12, C_13)=k1_xboole_0 | ~v1_funct_2(C_13, k1_xboole_0, B_12) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_12))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.17/1.28  tff(c_138, plain, (![B_43, C_44]: (k1_relset_1('#skF_1', B_43, C_44)='#skF_1' | ~v1_funct_2(C_44, '#skF_1', B_43) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_43))))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_110, c_110, c_110, c_20])).
% 2.17/1.28  tff(c_141, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_138])).
% 2.17/1.28  tff(c_144, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_55, c_141])).
% 2.17/1.28  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_144])).
% 2.17/1.28  tff(c_147, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_83])).
% 2.17/1.28  tff(c_8, plain, (![B_7, A_6]: (k1_funct_1(k2_funct_1(B_7), k1_funct_1(B_7, A_6))=A_6 | ~r2_hidden(A_6, k1_relat_1(B_7)) | ~v2_funct_1(B_7) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.28  tff(c_155, plain, ('#skF_3'='#skF_4' | ~r2_hidden('#skF_4', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_147, c_8])).
% 2.17/1.28  tff(c_162, plain, ('#skF_3'='#skF_4' | ~r2_hidden('#skF_4', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38, c_32, c_155])).
% 2.17/1.28  tff(c_163, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_24, c_162])).
% 2.17/1.28  tff(c_194, plain, (~r2_hidden('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_163])).
% 2.17/1.28  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_194])).
% 2.17/1.28  tff(c_201, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(splitRight, [status(thm)], [c_192])).
% 2.17/1.28  tff(c_200, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_192])).
% 2.17/1.28  tff(c_221, plain, (![B_56, C_57]: (k1_relset_1('#skF_1', B_56, C_57)='#skF_1' | ~v1_funct_2(C_57, '#skF_1', B_56) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_56))))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_200, c_200, c_20])).
% 2.17/1.28  tff(c_224, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_221])).
% 2.17/1.28  tff(c_227, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_55, c_224])).
% 2.17/1.28  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_227])).
% 2.17/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.28  
% 2.17/1.28  Inference rules
% 2.17/1.28  ----------------------
% 2.17/1.28  #Ref     : 0
% 2.17/1.28  #Sup     : 34
% 2.17/1.28  #Fact    : 0
% 2.17/1.28  #Define  : 0
% 2.17/1.28  #Split   : 3
% 2.17/1.28  #Chain   : 0
% 2.17/1.28  #Close   : 0
% 2.17/1.28  
% 2.17/1.28  Ordering : KBO
% 2.17/1.28  
% 2.17/1.28  Simplification rules
% 2.17/1.28  ----------------------
% 2.17/1.28  #Subsume      : 1
% 2.17/1.28  #Demod        : 69
% 2.17/1.28  #Tautology    : 20
% 2.17/1.28  #SimpNegUnit  : 4
% 2.17/1.28  #BackRed      : 16
% 2.17/1.28  
% 2.17/1.28  #Partial instantiations: 0
% 2.17/1.28  #Strategies tried      : 1
% 2.17/1.28  
% 2.17/1.28  Timing (in seconds)
% 2.17/1.28  ----------------------
% 2.17/1.28  Preprocessing        : 0.30
% 2.17/1.28  Parsing              : 0.15
% 2.17/1.28  CNF conversion       : 0.02
% 2.17/1.28  Main loop            : 0.19
% 2.17/1.28  Inferencing          : 0.07
% 2.17/1.28  Reduction            : 0.06
% 2.17/1.28  Demodulation         : 0.05
% 2.17/1.28  BG Simplification    : 0.01
% 2.17/1.28  Subsumption          : 0.04
% 2.17/1.28  Abstraction          : 0.01
% 2.17/1.28  MUC search           : 0.00
% 2.17/1.28  Cooper               : 0.00
% 2.17/1.28  Total                : 0.52
% 2.17/1.28  Index Insertion      : 0.00
% 2.17/1.28  Index Deletion       : 0.00
% 2.17/1.28  Index Matching       : 0.00
% 2.17/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
