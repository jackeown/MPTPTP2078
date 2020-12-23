%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:18 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 106 expanded)
%              Number of leaves         :   43 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 194 expanded)
%              Number of equality atoms :   27 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_68,axiom,(
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

tff(f_113,axiom,(
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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_76,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_277,plain,(
    ! [C_89,B_90,A_91] :
      ( v5_relat_1(C_89,B_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_281,plain,(
    v5_relat_1('#skF_9',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_76,c_277])).

tff(c_74,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_48,plain,(
    ! [A_28,B_29] : v1_relat_1(k2_zfmisc_1(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_222,plain,(
    ! [B_76,A_77] :
      ( v1_relat_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_77))
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_225,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_76,c_222])).

tff(c_228,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_225])).

tff(c_80,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_78,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_357,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_361,plain,(
    k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_357])).

tff(c_641,plain,(
    ! [B_150,A_151,C_152] :
      ( k1_xboole_0 = B_150
      | k1_relset_1(A_151,B_150,C_152) = A_151
      | ~ v1_funct_2(C_152,A_151,B_150)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_151,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_644,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_76,c_641])).

tff(c_647,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_361,c_644])).

tff(c_648,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_647])).

tff(c_50,plain,(
    ! [C_32,B_31,A_30] :
      ( m1_subset_1(k1_funct_1(C_32,B_31),A_30)
      | ~ r2_hidden(B_31,k1_relat_1(C_32))
      | ~ v1_funct_1(C_32)
      | ~ v5_relat_1(C_32,A_30)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_652,plain,(
    ! [B_31,A_30] :
      ( m1_subset_1(k1_funct_1('#skF_9',B_31),A_30)
      | ~ r2_hidden(B_31,'#skF_6')
      | ~ v1_funct_1('#skF_9')
      | ~ v5_relat_1('#skF_9',A_30)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_50])).

tff(c_662,plain,(
    ! [B_153,A_154] :
      ( m1_subset_1(k1_funct_1('#skF_9',B_153),A_154)
      | ~ r2_hidden(B_153,'#skF_6')
      | ~ v5_relat_1('#skF_9',A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_80,c_652])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_98,plain,(
    ! [B_51,A_52] :
      ( ~ r2_hidden(B_51,A_52)
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,(
    ! [C_10] : ~ v1_xboole_0(k1_tarski(C_10)) ),
    inference(resolution,[status(thm)],[c_10,c_98])).

tff(c_205,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(A_72,B_73)
      | v1_xboole_0(B_73)
      | ~ m1_subset_1(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_212,plain,(
    ! [A_72,A_6] :
      ( A_72 = A_6
      | v1_xboole_0(k1_tarski(A_6))
      | ~ m1_subset_1(A_72,k1_tarski(A_6)) ) ),
    inference(resolution,[status(thm)],[c_205,c_8])).

tff(c_219,plain,(
    ! [A_72,A_6] :
      ( A_72 = A_6
      | ~ m1_subset_1(A_72,k1_tarski(A_6)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_212])).

tff(c_718,plain,(
    ! [B_155,A_156] :
      ( k1_funct_1('#skF_9',B_155) = A_156
      | ~ r2_hidden(B_155,'#skF_6')
      | ~ v5_relat_1('#skF_9',k1_tarski(A_156)) ) ),
    inference(resolution,[status(thm)],[c_662,c_219])).

tff(c_742,plain,(
    ! [A_157] :
      ( k1_funct_1('#skF_9','#skF_8') = A_157
      | ~ v5_relat_1('#skF_9',k1_tarski(A_157)) ) ),
    inference(resolution,[status(thm)],[c_74,c_718])).

tff(c_745,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_281,c_742])).

tff(c_749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_745])).

tff(c_750,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_156,plain,(
    ! [B_62,A_63] :
      ( ~ r1_tarski(B_62,A_63)
      | ~ r2_hidden(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_175,plain,(
    ! [C_10] : ~ r1_tarski(k1_tarski(C_10),C_10) ),
    inference(resolution,[status(thm)],[c_10,c_156])).

tff(c_777,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_175])).

tff(c_798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_777])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:32:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.49  
% 3.03/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2
% 3.03/1.50  
% 3.03/1.50  %Foreground sorts:
% 3.03/1.50  
% 3.03/1.50  
% 3.03/1.50  %Background operators:
% 3.03/1.50  
% 3.03/1.50  
% 3.03/1.50  %Foreground operators:
% 3.03/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.03/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.03/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.03/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.03/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.03/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.03/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.03/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.03/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.03/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.03/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.03/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.03/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.03/1.50  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.03/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.03/1.50  tff('#skF_9', type, '#skF_9': $i).
% 3.03/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.03/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.03/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.03/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.03/1.50  tff('#skF_8', type, '#skF_8': $i).
% 3.03/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.03/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.03/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.03/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.03/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.03/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.03/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.50  
% 3.03/1.51  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.03/1.51  tff(f_124, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.03/1.51  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.03/1.51  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.03/1.51  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.03/1.51  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.03/1.51  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.03/1.51  tff(f_80, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 3.03/1.51  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.03/1.51  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.03/1.51  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.03/1.51  tff(f_85, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.03/1.51  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.03/1.51  tff(c_72, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.03/1.51  tff(c_76, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.03/1.51  tff(c_277, plain, (![C_89, B_90, A_91]: (v5_relat_1(C_89, B_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.03/1.51  tff(c_281, plain, (v5_relat_1('#skF_9', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_76, c_277])).
% 3.03/1.51  tff(c_74, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.03/1.51  tff(c_48, plain, (![A_28, B_29]: (v1_relat_1(k2_zfmisc_1(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.03/1.51  tff(c_222, plain, (![B_76, A_77]: (v1_relat_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_77)) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.03/1.51  tff(c_225, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_76, c_222])).
% 3.03/1.51  tff(c_228, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_225])).
% 3.03/1.51  tff(c_80, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.03/1.51  tff(c_78, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.03/1.51  tff(c_357, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.03/1.51  tff(c_361, plain, (k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_76, c_357])).
% 3.03/1.51  tff(c_641, plain, (![B_150, A_151, C_152]: (k1_xboole_0=B_150 | k1_relset_1(A_151, B_150, C_152)=A_151 | ~v1_funct_2(C_152, A_151, B_150) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_151, B_150))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.03/1.51  tff(c_644, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_76, c_641])).
% 3.03/1.51  tff(c_647, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_361, c_644])).
% 3.03/1.51  tff(c_648, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_647])).
% 3.03/1.51  tff(c_50, plain, (![C_32, B_31, A_30]: (m1_subset_1(k1_funct_1(C_32, B_31), A_30) | ~r2_hidden(B_31, k1_relat_1(C_32)) | ~v1_funct_1(C_32) | ~v5_relat_1(C_32, A_30) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.03/1.51  tff(c_652, plain, (![B_31, A_30]: (m1_subset_1(k1_funct_1('#skF_9', B_31), A_30) | ~r2_hidden(B_31, '#skF_6') | ~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', A_30) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_648, c_50])).
% 3.03/1.51  tff(c_662, plain, (![B_153, A_154]: (m1_subset_1(k1_funct_1('#skF_9', B_153), A_154) | ~r2_hidden(B_153, '#skF_6') | ~v5_relat_1('#skF_9', A_154))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_80, c_652])).
% 3.03/1.51  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.03/1.51  tff(c_98, plain, (![B_51, A_52]: (~r2_hidden(B_51, A_52) | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.03/1.51  tff(c_109, plain, (![C_10]: (~v1_xboole_0(k1_tarski(C_10)))), inference(resolution, [status(thm)], [c_10, c_98])).
% 3.03/1.51  tff(c_205, plain, (![A_72, B_73]: (r2_hidden(A_72, B_73) | v1_xboole_0(B_73) | ~m1_subset_1(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.03/1.51  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.03/1.51  tff(c_212, plain, (![A_72, A_6]: (A_72=A_6 | v1_xboole_0(k1_tarski(A_6)) | ~m1_subset_1(A_72, k1_tarski(A_6)))), inference(resolution, [status(thm)], [c_205, c_8])).
% 3.03/1.51  tff(c_219, plain, (![A_72, A_6]: (A_72=A_6 | ~m1_subset_1(A_72, k1_tarski(A_6)))), inference(negUnitSimplification, [status(thm)], [c_109, c_212])).
% 3.03/1.51  tff(c_718, plain, (![B_155, A_156]: (k1_funct_1('#skF_9', B_155)=A_156 | ~r2_hidden(B_155, '#skF_6') | ~v5_relat_1('#skF_9', k1_tarski(A_156)))), inference(resolution, [status(thm)], [c_662, c_219])).
% 3.03/1.51  tff(c_742, plain, (![A_157]: (k1_funct_1('#skF_9', '#skF_8')=A_157 | ~v5_relat_1('#skF_9', k1_tarski(A_157)))), inference(resolution, [status(thm)], [c_74, c_718])).
% 3.03/1.51  tff(c_745, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_281, c_742])).
% 3.03/1.51  tff(c_749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_745])).
% 3.03/1.51  tff(c_750, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_647])).
% 3.03/1.51  tff(c_156, plain, (![B_62, A_63]: (~r1_tarski(B_62, A_63) | ~r2_hidden(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.03/1.51  tff(c_175, plain, (![C_10]: (~r1_tarski(k1_tarski(C_10), C_10))), inference(resolution, [status(thm)], [c_10, c_156])).
% 3.03/1.51  tff(c_777, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_750, c_175])).
% 3.03/1.51  tff(c_798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_777])).
% 3.03/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.51  
% 3.03/1.51  Inference rules
% 3.03/1.51  ----------------------
% 3.03/1.51  #Ref     : 0
% 3.03/1.51  #Sup     : 148
% 3.03/1.51  #Fact    : 2
% 3.03/1.51  #Define  : 0
% 3.03/1.51  #Split   : 1
% 3.03/1.51  #Chain   : 0
% 3.03/1.51  #Close   : 0
% 3.03/1.51  
% 3.03/1.51  Ordering : KBO
% 3.03/1.51  
% 3.03/1.51  Simplification rules
% 3.03/1.51  ----------------------
% 3.03/1.51  #Subsume      : 20
% 3.03/1.51  #Demod        : 75
% 3.03/1.51  #Tautology    : 64
% 3.03/1.51  #SimpNegUnit  : 15
% 3.03/1.51  #BackRed      : 5
% 3.03/1.51  
% 3.03/1.51  #Partial instantiations: 0
% 3.03/1.51  #Strategies tried      : 1
% 3.03/1.51  
% 3.03/1.51  Timing (in seconds)
% 3.03/1.51  ----------------------
% 3.03/1.51  Preprocessing        : 0.38
% 3.03/1.51  Parsing              : 0.19
% 3.03/1.51  CNF conversion       : 0.03
% 3.03/1.51  Main loop            : 0.34
% 3.03/1.51  Inferencing          : 0.12
% 3.03/1.51  Reduction            : 0.11
% 3.03/1.51  Demodulation         : 0.07
% 3.03/1.51  BG Simplification    : 0.02
% 3.03/1.51  Subsumption          : 0.06
% 3.03/1.51  Abstraction          : 0.02
% 3.03/1.51  MUC search           : 0.00
% 3.03/1.51  Cooper               : 0.00
% 3.03/1.51  Total                : 0.75
% 3.03/1.51  Index Insertion      : 0.00
% 3.03/1.51  Index Deletion       : 0.00
% 3.03/1.51  Index Matching       : 0.00
% 3.03/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
