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
% DateTime   : Thu Dec  3 10:15:18 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 102 expanded)
%              Number of leaves         :   42 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 187 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_110,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_52,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_74,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_198,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_202,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_74,c_198])).

tff(c_72,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_46,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_143,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_146,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_74,c_143])).

tff(c_149,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_146])).

tff(c_78,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_76,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_209,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_213,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_209])).

tff(c_478,plain,(
    ! [B_135,A_136,C_137] :
      ( k1_xboole_0 = B_135
      | k1_relset_1(A_136,B_135,C_137) = A_136
      | ~ v1_funct_2(C_137,A_136,B_135)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_136,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_481,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_74,c_478])).

tff(c_484,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_213,c_481])).

tff(c_485,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_484])).

tff(c_48,plain,(
    ! [C_29,B_28,A_27] :
      ( m1_subset_1(k1_funct_1(C_29,B_28),A_27)
      | ~ r2_hidden(B_28,k1_relat_1(C_29))
      | ~ v1_funct_1(C_29)
      | ~ v5_relat_1(C_29,A_27)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_489,plain,(
    ! [B_28,A_27] :
      ( m1_subset_1(k1_funct_1('#skF_8',B_28),A_27)
      | ~ r2_hidden(B_28,'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_27)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_48])).

tff(c_499,plain,(
    ! [B_138,A_139] :
      ( m1_subset_1(k1_funct_1('#skF_8',B_138),A_139)
      | ~ r2_hidden(B_138,'#skF_5')
      | ~ v5_relat_1('#skF_8',A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_78,c_489])).

tff(c_40,plain,(
    ! [A_19] : ~ v1_xboole_0(k1_tarski(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_150,plain,(
    ! [A_64,B_65] :
      ( r2_hidden(A_64,B_65)
      | v1_xboole_0(B_65)
      | ~ m1_subset_1(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_154,plain,(
    ! [A_64,A_2] :
      ( A_64 = A_2
      | v1_xboole_0(k1_tarski(A_2))
      | ~ m1_subset_1(A_64,k1_tarski(A_2)) ) ),
    inference(resolution,[status(thm)],[c_150,c_4])).

tff(c_160,plain,(
    ! [A_64,A_2] :
      ( A_64 = A_2
      | ~ m1_subset_1(A_64,k1_tarski(A_2)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_154])).

tff(c_556,plain,(
    ! [B_140,A_141] :
      ( k1_funct_1('#skF_8',B_140) = A_141
      | ~ r2_hidden(B_140,'#skF_5')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_141)) ) ),
    inference(resolution,[status(thm)],[c_499,c_160])).

tff(c_576,plain,(
    ! [A_142] :
      ( k1_funct_1('#skF_8','#skF_7') = A_142
      | ~ v5_relat_1('#skF_8',k1_tarski(A_142)) ) ),
    inference(resolution,[status(thm)],[c_72,c_556])).

tff(c_579,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_202,c_576])).

tff(c_583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_579])).

tff(c_584,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_484])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102,plain,(
    ! [B_51,A_52] :
      ( ~ r1_tarski(B_51,A_52)
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_117,plain,(
    ! [C_6] : ~ r1_tarski(k1_tarski(C_6),C_6) ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_608,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_117])).

tff(c_621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_608])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:42:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.38  
% 2.85/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.39  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 2.85/1.39  
% 2.85/1.39  %Foreground sorts:
% 2.85/1.39  
% 2.85/1.39  
% 2.85/1.39  %Background operators:
% 2.85/1.39  
% 2.85/1.39  
% 2.85/1.39  %Foreground operators:
% 2.85/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.85/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.85/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.85/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.85/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.85/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.85/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.85/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.85/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.85/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.85/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.85/1.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.85/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.85/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.85/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.85/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.85/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.85/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.85/1.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.85/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.85/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.85/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.85/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.39  
% 2.85/1.40  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.85/1.40  tff(f_121, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.85/1.40  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.85/1.40  tff(f_67, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.85/1.40  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.85/1.40  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.85/1.40  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.85/1.40  tff(f_77, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 2.85/1.40  tff(f_52, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.85/1.40  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.85/1.40  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.85/1.40  tff(f_82, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.85/1.40  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.85/1.40  tff(c_70, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.85/1.40  tff(c_74, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.85/1.40  tff(c_198, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.85/1.40  tff(c_202, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_198])).
% 2.85/1.40  tff(c_72, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.85/1.40  tff(c_46, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.85/1.40  tff(c_143, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.85/1.40  tff(c_146, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_74, c_143])).
% 2.85/1.40  tff(c_149, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_146])).
% 2.85/1.40  tff(c_78, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.85/1.40  tff(c_76, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.85/1.40  tff(c_209, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.85/1.40  tff(c_213, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_74, c_209])).
% 2.85/1.40  tff(c_478, plain, (![B_135, A_136, C_137]: (k1_xboole_0=B_135 | k1_relset_1(A_136, B_135, C_137)=A_136 | ~v1_funct_2(C_137, A_136, B_135) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_136, B_135))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.85/1.40  tff(c_481, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_478])).
% 2.85/1.40  tff(c_484, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_213, c_481])).
% 2.85/1.40  tff(c_485, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_484])).
% 2.85/1.40  tff(c_48, plain, (![C_29, B_28, A_27]: (m1_subset_1(k1_funct_1(C_29, B_28), A_27) | ~r2_hidden(B_28, k1_relat_1(C_29)) | ~v1_funct_1(C_29) | ~v5_relat_1(C_29, A_27) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.85/1.40  tff(c_489, plain, (![B_28, A_27]: (m1_subset_1(k1_funct_1('#skF_8', B_28), A_27) | ~r2_hidden(B_28, '#skF_5') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_27) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_485, c_48])).
% 2.85/1.40  tff(c_499, plain, (![B_138, A_139]: (m1_subset_1(k1_funct_1('#skF_8', B_138), A_139) | ~r2_hidden(B_138, '#skF_5') | ~v5_relat_1('#skF_8', A_139))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_78, c_489])).
% 2.85/1.40  tff(c_40, plain, (![A_19]: (~v1_xboole_0(k1_tarski(A_19)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.85/1.40  tff(c_150, plain, (![A_64, B_65]: (r2_hidden(A_64, B_65) | v1_xboole_0(B_65) | ~m1_subset_1(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.85/1.40  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.85/1.40  tff(c_154, plain, (![A_64, A_2]: (A_64=A_2 | v1_xboole_0(k1_tarski(A_2)) | ~m1_subset_1(A_64, k1_tarski(A_2)))), inference(resolution, [status(thm)], [c_150, c_4])).
% 2.85/1.40  tff(c_160, plain, (![A_64, A_2]: (A_64=A_2 | ~m1_subset_1(A_64, k1_tarski(A_2)))), inference(negUnitSimplification, [status(thm)], [c_40, c_154])).
% 2.85/1.40  tff(c_556, plain, (![B_140, A_141]: (k1_funct_1('#skF_8', B_140)=A_141 | ~r2_hidden(B_140, '#skF_5') | ~v5_relat_1('#skF_8', k1_tarski(A_141)))), inference(resolution, [status(thm)], [c_499, c_160])).
% 2.85/1.40  tff(c_576, plain, (![A_142]: (k1_funct_1('#skF_8', '#skF_7')=A_142 | ~v5_relat_1('#skF_8', k1_tarski(A_142)))), inference(resolution, [status(thm)], [c_72, c_556])).
% 2.85/1.40  tff(c_579, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_202, c_576])).
% 2.85/1.40  tff(c_583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_579])).
% 2.85/1.40  tff(c_584, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_484])).
% 2.85/1.40  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.85/1.40  tff(c_102, plain, (![B_51, A_52]: (~r1_tarski(B_51, A_52) | ~r2_hidden(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.85/1.40  tff(c_117, plain, (![C_6]: (~r1_tarski(k1_tarski(C_6), C_6))), inference(resolution, [status(thm)], [c_6, c_102])).
% 2.85/1.40  tff(c_608, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_584, c_117])).
% 2.85/1.40  tff(c_621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_608])).
% 2.85/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.40  
% 2.85/1.40  Inference rules
% 2.85/1.40  ----------------------
% 2.85/1.40  #Ref     : 0
% 2.85/1.40  #Sup     : 113
% 2.85/1.40  #Fact    : 0
% 2.85/1.40  #Define  : 0
% 2.85/1.40  #Split   : 3
% 2.85/1.40  #Chain   : 0
% 2.85/1.40  #Close   : 0
% 2.85/1.40  
% 2.85/1.40  Ordering : KBO
% 2.85/1.40  
% 2.85/1.40  Simplification rules
% 2.85/1.40  ----------------------
% 2.85/1.40  #Subsume      : 16
% 2.85/1.40  #Demod        : 42
% 2.85/1.40  #Tautology    : 38
% 2.85/1.40  #SimpNegUnit  : 5
% 2.85/1.40  #BackRed      : 5
% 2.85/1.40  
% 2.85/1.40  #Partial instantiations: 0
% 2.85/1.40  #Strategies tried      : 1
% 2.85/1.40  
% 2.85/1.40  Timing (in seconds)
% 2.85/1.40  ----------------------
% 2.85/1.40  Preprocessing        : 0.33
% 2.85/1.40  Parsing              : 0.17
% 2.85/1.40  CNF conversion       : 0.02
% 2.85/1.40  Main loop            : 0.31
% 2.85/1.40  Inferencing          : 0.11
% 2.85/1.41  Reduction            : 0.10
% 2.85/1.41  Demodulation         : 0.07
% 2.85/1.41  BG Simplification    : 0.02
% 2.85/1.41  Subsumption          : 0.06
% 2.85/1.41  Abstraction          : 0.02
% 2.85/1.41  MUC search           : 0.00
% 2.85/1.41  Cooper               : 0.00
% 2.85/1.41  Total                : 0.67
% 2.85/1.41  Index Insertion      : 0.00
% 2.85/1.41  Index Deletion       : 0.00
% 2.85/1.41  Index Matching       : 0.00
% 2.85/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
