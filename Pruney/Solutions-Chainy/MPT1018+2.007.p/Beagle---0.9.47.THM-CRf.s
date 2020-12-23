%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:46 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 275 expanded)
%              Number of leaves         :   26 ( 111 expanded)
%              Depth                    :    9
%              Number of atoms          :  113 ( 916 expanded)
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

tff(f_81,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_63,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_26,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_46,plain,(
    ! [A_17,B_18,C_19] :
      ( k1_relset_1(A_17,B_18,C_19) = k1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_168,plain,(
    ! [B_44,A_45,C_46] :
      ( k1_xboole_0 = B_44
      | k1_relset_1(A_45,B_44,C_46) = A_45
      | ~ v1_funct_2(C_46,A_45,B_44)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_45,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_171,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_168])).

tff(c_174,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_50,c_171])).

tff(c_175,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_22,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_41,plain,(
    ! [C_14,A_15,B_16] :
      ( v1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_45,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_41])).

tff(c_36,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_98,plain,(
    ! [B_34,A_35,C_36] :
      ( k1_xboole_0 = B_34
      | k1_relset_1(A_35,B_34,C_36) = A_35
      | ~ v1_funct_2(C_36,A_35,B_34)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_35,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_101,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_98])).

tff(c_104,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_50,c_101])).

tff(c_105,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_24,plain,(
    k1_funct_1('#skF_2','#skF_3') = k1_funct_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_74,plain,(
    ! [B_32,A_33] :
      ( k1_funct_1(k2_funct_1(B_32),k1_funct_1(B_32,A_33)) = A_33
      | ~ r2_hidden(A_33,k1_relat_1(B_32))
      | ~ v2_funct_1(B_32)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_74])).

tff(c_96,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_36,c_30,c_92])).

tff(c_97,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_106,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_97])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_106])).

tff(c_112,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_111,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_18,plain,(
    ! [B_10,C_11] :
      ( k1_relset_1(k1_xboole_0,B_10,C_11) = k1_xboole_0
      | ~ v1_funct_2(C_11,k1_xboole_0,B_10)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_138,plain,(
    ! [B_42,C_43] :
      ( k1_relset_1('#skF_1',B_42,C_43) = '#skF_1'
      | ~ v1_funct_2(C_43,'#skF_1',B_42)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_42))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_111,c_111,c_111,c_18])).

tff(c_141,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_138])).

tff(c_144,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_50,c_141])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_144])).

tff(c_147,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( k1_funct_1(k2_funct_1(B_2),k1_funct_1(B_2,A_1)) = A_1
      | ~ r2_hidden(A_1,k1_relat_1(B_2))
      | ~ v2_funct_1(B_2)
      | ~ v1_funct_1(B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_155,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_4])).

tff(c_162,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_36,c_30,c_155])).

tff(c_163,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_162])).

tff(c_176,plain,(
    ~ r2_hidden('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_163])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_176])).

tff(c_183,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_182,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_204,plain,(
    ! [B_50,C_51] :
      ( k1_relset_1('#skF_1',B_50,C_51) = '#skF_1'
      | ~ v1_funct_2(C_51,'#skF_1',B_50)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_50))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_182,c_182,c_182,c_18])).

tff(c_207,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_204])).

tff(c_210,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_50,c_207])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:11:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.22  
% 2.20/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.23  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.20/1.23  
% 2.20/1.23  %Foreground sorts:
% 2.20/1.23  
% 2.20/1.23  
% 2.20/1.23  %Background operators:
% 2.20/1.23  
% 2.20/1.23  
% 2.20/1.23  %Foreground operators:
% 2.20/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.20/1.23  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.20/1.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.20/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.23  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.20/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.20/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.20/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.20/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.20/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.20/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.23  
% 2.31/1.24  tff(f_81, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 2.31/1.24  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.31/1.24  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.31/1.24  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.31/1.24  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 2.31/1.24  tff(c_26, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.31/1.24  tff(c_34, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.31/1.24  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.31/1.24  tff(c_46, plain, (![A_17, B_18, C_19]: (k1_relset_1(A_17, B_18, C_19)=k1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.31/1.24  tff(c_50, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_46])).
% 2.31/1.24  tff(c_168, plain, (![B_44, A_45, C_46]: (k1_xboole_0=B_44 | k1_relset_1(A_45, B_44, C_46)=A_45 | ~v1_funct_2(C_46, A_45, B_44) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_45, B_44))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.31/1.24  tff(c_171, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_168])).
% 2.31/1.24  tff(c_174, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_50, c_171])).
% 2.31/1.24  tff(c_175, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_174])).
% 2.31/1.24  tff(c_22, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.31/1.24  tff(c_41, plain, (![C_14, A_15, B_16]: (v1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.24  tff(c_45, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_41])).
% 2.31/1.24  tff(c_36, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.31/1.24  tff(c_30, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.31/1.24  tff(c_28, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.31/1.24  tff(c_98, plain, (![B_34, A_35, C_36]: (k1_xboole_0=B_34 | k1_relset_1(A_35, B_34, C_36)=A_35 | ~v1_funct_2(C_36, A_35, B_34) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_35, B_34))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.31/1.24  tff(c_101, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_98])).
% 2.31/1.24  tff(c_104, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_50, c_101])).
% 2.31/1.24  tff(c_105, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_104])).
% 2.31/1.24  tff(c_24, plain, (k1_funct_1('#skF_2', '#skF_3')=k1_funct_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.31/1.24  tff(c_74, plain, (![B_32, A_33]: (k1_funct_1(k2_funct_1(B_32), k1_funct_1(B_32, A_33))=A_33 | ~r2_hidden(A_33, k1_relat_1(B_32)) | ~v2_funct_1(B_32) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.31/1.24  tff(c_92, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | ~r2_hidden('#skF_3', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24, c_74])).
% 2.31/1.24  tff(c_96, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | ~r2_hidden('#skF_3', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_36, c_30, c_92])).
% 2.31/1.24  tff(c_97, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_96])).
% 2.31/1.24  tff(c_106, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_97])).
% 2.31/1.24  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_106])).
% 2.31/1.24  tff(c_112, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(splitRight, [status(thm)], [c_104])).
% 2.31/1.24  tff(c_111, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_104])).
% 2.31/1.24  tff(c_18, plain, (![B_10, C_11]: (k1_relset_1(k1_xboole_0, B_10, C_11)=k1_xboole_0 | ~v1_funct_2(C_11, k1_xboole_0, B_10) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_10))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.31/1.24  tff(c_138, plain, (![B_42, C_43]: (k1_relset_1('#skF_1', B_42, C_43)='#skF_1' | ~v1_funct_2(C_43, '#skF_1', B_42) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_42))))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_111, c_111, c_111, c_18])).
% 2.31/1.24  tff(c_141, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_138])).
% 2.31/1.24  tff(c_144, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_50, c_141])).
% 2.31/1.24  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_144])).
% 2.31/1.24  tff(c_147, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_96])).
% 2.31/1.24  tff(c_4, plain, (![B_2, A_1]: (k1_funct_1(k2_funct_1(B_2), k1_funct_1(B_2, A_1))=A_1 | ~r2_hidden(A_1, k1_relat_1(B_2)) | ~v2_funct_1(B_2) | ~v1_funct_1(B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.31/1.24  tff(c_155, plain, ('#skF_3'='#skF_4' | ~r2_hidden('#skF_4', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_147, c_4])).
% 2.31/1.24  tff(c_162, plain, ('#skF_3'='#skF_4' | ~r2_hidden('#skF_4', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_36, c_30, c_155])).
% 2.31/1.24  tff(c_163, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_22, c_162])).
% 2.31/1.24  tff(c_176, plain, (~r2_hidden('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_175, c_163])).
% 2.31/1.24  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_176])).
% 2.31/1.24  tff(c_183, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(splitRight, [status(thm)], [c_174])).
% 2.31/1.24  tff(c_182, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_174])).
% 2.31/1.24  tff(c_204, plain, (![B_50, C_51]: (k1_relset_1('#skF_1', B_50, C_51)='#skF_1' | ~v1_funct_2(C_51, '#skF_1', B_50) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_50))))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_182, c_182, c_182, c_18])).
% 2.31/1.24  tff(c_207, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_204])).
% 2.31/1.24  tff(c_210, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_50, c_207])).
% 2.31/1.24  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_210])).
% 2.31/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.24  
% 2.31/1.24  Inference rules
% 2.31/1.24  ----------------------
% 2.31/1.24  #Ref     : 0
% 2.31/1.24  #Sup     : 31
% 2.31/1.24  #Fact    : 0
% 2.31/1.24  #Define  : 0
% 2.31/1.24  #Split   : 4
% 2.31/1.24  #Chain   : 0
% 2.31/1.24  #Close   : 0
% 2.31/1.24  
% 2.31/1.24  Ordering : KBO
% 2.31/1.24  
% 2.31/1.24  Simplification rules
% 2.31/1.24  ----------------------
% 2.31/1.24  #Subsume      : 2
% 2.31/1.24  #Demod        : 68
% 2.31/1.24  #Tautology    : 17
% 2.31/1.24  #SimpNegUnit  : 4
% 2.31/1.24  #BackRed      : 17
% 2.31/1.24  
% 2.31/1.24  #Partial instantiations: 0
% 2.31/1.24  #Strategies tried      : 1
% 2.31/1.24  
% 2.31/1.24  Timing (in seconds)
% 2.31/1.24  ----------------------
% 2.31/1.24  Preprocessing        : 0.30
% 2.31/1.24  Parsing              : 0.16
% 2.31/1.24  CNF conversion       : 0.02
% 2.31/1.24  Main loop            : 0.19
% 2.31/1.24  Inferencing          : 0.07
% 2.31/1.24  Reduction            : 0.06
% 2.31/1.24  Demodulation         : 0.04
% 2.31/1.24  BG Simplification    : 0.02
% 2.31/1.24  Subsumption          : 0.03
% 2.31/1.24  Abstraction          : 0.01
% 2.31/1.25  MUC search           : 0.00
% 2.31/1.25  Cooper               : 0.00
% 2.31/1.25  Total                : 0.53
% 2.31/1.25  Index Insertion      : 0.00
% 2.31/1.25  Index Deletion       : 0.00
% 2.31/1.25  Index Matching       : 0.00
% 2.31/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
