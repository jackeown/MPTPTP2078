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
% DateTime   : Thu Dec  3 10:15:10 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   68 (  93 expanded)
%              Number of leaves         :   37 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   93 ( 174 expanded)
%              Number of equality atoms :   27 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
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
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_48,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_102,plain,(
    ! [C_47,B_48,A_49] :
      ( v5_relat_1(C_47,B_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_49,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_106,plain,(
    v5_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_102])).

tff(c_50,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_92,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_96,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_92])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_130,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_134,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_130])).

tff(c_199,plain,(
    ! [B_85,A_86,C_87] :
      ( k1_xboole_0 = B_85
      | k1_relset_1(A_86,B_85,C_87) = A_86
      | ~ v1_funct_2(C_87,A_86,B_85)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_202,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_199])).

tff(c_205,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_134,c_202])).

tff(c_206,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_26,plain,(
    ! [C_17,B_16,A_15] :
      ( m1_subset_1(k1_funct_1(C_17,B_16),A_15)
      | ~ r2_hidden(B_16,k1_relat_1(C_17))
      | ~ v1_funct_1(C_17)
      | ~ v5_relat_1(C_17,A_15)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_210,plain,(
    ! [B_16,A_15] :
      ( m1_subset_1(k1_funct_1('#skF_6',B_16),A_15)
      | ~ r2_hidden(B_16,'#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_15)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_26])).

tff(c_220,plain,(
    ! [B_88,A_89] :
      ( m1_subset_1(k1_funct_1('#skF_6',B_88),A_89)
      | ~ r2_hidden(B_88,'#skF_3')
      | ~ v5_relat_1('#skF_6',A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_56,c_210])).

tff(c_22,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_83,plain,(
    ! [A_37,B_38] :
      ( r2_hidden(A_37,B_38)
      | v1_xboole_0(B_38)
      | ~ m1_subset_1(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    ! [A_37,A_1] :
      ( A_37 = A_1
      | v1_xboole_0(k1_tarski(A_1))
      | ~ m1_subset_1(A_37,k1_tarski(A_1)) ) ),
    inference(resolution,[status(thm)],[c_83,c_4])).

tff(c_90,plain,(
    ! [A_37,A_1] :
      ( A_37 = A_1
      | ~ m1_subset_1(A_37,k1_tarski(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_87])).

tff(c_271,plain,(
    ! [B_90,A_91] :
      ( k1_funct_1('#skF_6',B_90) = A_91
      | ~ r2_hidden(B_90,'#skF_3')
      | ~ v5_relat_1('#skF_6',k1_tarski(A_91)) ) ),
    inference(resolution,[status(thm)],[c_220,c_90])).

tff(c_287,plain,(
    ! [A_92] :
      ( k1_funct_1('#skF_6','#skF_5') = A_92
      | ~ v5_relat_1('#skF_6',k1_tarski(A_92)) ) ),
    inference(resolution,[status(thm)],[c_50,c_271])).

tff(c_290,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_106,c_287])).

tff(c_294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_290])).

tff(c_295,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_327,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_22])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:47:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.21  
% 2.17/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.22  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.17/1.22  
% 2.17/1.22  %Foreground sorts:
% 2.17/1.22  
% 2.17/1.22  
% 2.17/1.22  %Background operators:
% 2.17/1.22  
% 2.17/1.22  
% 2.17/1.22  %Foreground operators:
% 2.17/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.17/1.22  tff('#skF_6', type, '#skF_6': $i).
% 2.17/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.22  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.17/1.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.17/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.17/1.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.17/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.17/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.22  
% 2.36/1.23  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.36/1.23  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.36/1.23  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.36/1.23  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.36/1.23  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.36/1.23  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.36/1.23  tff(f_58, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 2.36/1.23  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.36/1.23  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.36/1.23  tff(f_33, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.36/1.23  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.36/1.23  tff(c_48, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.36/1.23  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.36/1.23  tff(c_102, plain, (![C_47, B_48, A_49]: (v5_relat_1(C_47, B_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_49, B_48))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.36/1.23  tff(c_106, plain, (v5_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_102])).
% 2.36/1.23  tff(c_50, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.36/1.23  tff(c_92, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.36/1.23  tff(c_96, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_92])).
% 2.36/1.23  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.36/1.23  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.36/1.23  tff(c_130, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.36/1.23  tff(c_134, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_130])).
% 2.36/1.23  tff(c_199, plain, (![B_85, A_86, C_87]: (k1_xboole_0=B_85 | k1_relset_1(A_86, B_85, C_87)=A_86 | ~v1_funct_2(C_87, A_86, B_85) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.36/1.23  tff(c_202, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_199])).
% 2.36/1.23  tff(c_205, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_134, c_202])).
% 2.36/1.23  tff(c_206, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_205])).
% 2.36/1.23  tff(c_26, plain, (![C_17, B_16, A_15]: (m1_subset_1(k1_funct_1(C_17, B_16), A_15) | ~r2_hidden(B_16, k1_relat_1(C_17)) | ~v1_funct_1(C_17) | ~v5_relat_1(C_17, A_15) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.36/1.23  tff(c_210, plain, (![B_16, A_15]: (m1_subset_1(k1_funct_1('#skF_6', B_16), A_15) | ~r2_hidden(B_16, '#skF_3') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_15) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_206, c_26])).
% 2.36/1.23  tff(c_220, plain, (![B_88, A_89]: (m1_subset_1(k1_funct_1('#skF_6', B_88), A_89) | ~r2_hidden(B_88, '#skF_3') | ~v5_relat_1('#skF_6', A_89))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_56, c_210])).
% 2.36/1.23  tff(c_22, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.36/1.23  tff(c_83, plain, (![A_37, B_38]: (r2_hidden(A_37, B_38) | v1_xboole_0(B_38) | ~m1_subset_1(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.36/1.23  tff(c_4, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.23  tff(c_87, plain, (![A_37, A_1]: (A_37=A_1 | v1_xboole_0(k1_tarski(A_1)) | ~m1_subset_1(A_37, k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_83, c_4])).
% 2.36/1.23  tff(c_90, plain, (![A_37, A_1]: (A_37=A_1 | ~m1_subset_1(A_37, k1_tarski(A_1)))), inference(negUnitSimplification, [status(thm)], [c_22, c_87])).
% 2.36/1.23  tff(c_271, plain, (![B_90, A_91]: (k1_funct_1('#skF_6', B_90)=A_91 | ~r2_hidden(B_90, '#skF_3') | ~v5_relat_1('#skF_6', k1_tarski(A_91)))), inference(resolution, [status(thm)], [c_220, c_90])).
% 2.36/1.23  tff(c_287, plain, (![A_92]: (k1_funct_1('#skF_6', '#skF_5')=A_92 | ~v5_relat_1('#skF_6', k1_tarski(A_92)))), inference(resolution, [status(thm)], [c_50, c_271])).
% 2.36/1.23  tff(c_290, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_106, c_287])).
% 2.36/1.23  tff(c_294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_290])).
% 2.36/1.23  tff(c_295, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_205])).
% 2.36/1.23  tff(c_327, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_295, c_22])).
% 2.36/1.23  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_327])).
% 2.36/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.23  
% 2.36/1.23  Inference rules
% 2.36/1.23  ----------------------
% 2.36/1.23  #Ref     : 0
% 2.36/1.23  #Sup     : 59
% 2.36/1.23  #Fact    : 0
% 2.36/1.23  #Define  : 0
% 2.36/1.23  #Split   : 1
% 2.36/1.23  #Chain   : 0
% 2.36/1.23  #Close   : 0
% 2.36/1.23  
% 2.36/1.23  Ordering : KBO
% 2.36/1.23  
% 2.36/1.23  Simplification rules
% 2.36/1.23  ----------------------
% 2.36/1.23  #Subsume      : 0
% 2.36/1.23  #Demod        : 28
% 2.36/1.23  #Tautology    : 20
% 2.36/1.23  #SimpNegUnit  : 3
% 2.36/1.23  #BackRed      : 5
% 2.36/1.23  
% 2.36/1.23  #Partial instantiations: 0
% 2.36/1.23  #Strategies tried      : 1
% 2.36/1.23  
% 2.36/1.23  Timing (in seconds)
% 2.36/1.23  ----------------------
% 2.36/1.23  Preprocessing        : 0.30
% 2.36/1.23  Parsing              : 0.15
% 2.36/1.23  CNF conversion       : 0.02
% 2.36/1.23  Main loop            : 0.23
% 2.36/1.23  Inferencing          : 0.08
% 2.36/1.23  Reduction            : 0.07
% 2.36/1.23  Demodulation         : 0.04
% 2.36/1.23  BG Simplification    : 0.02
% 2.36/1.23  Subsumption          : 0.04
% 2.36/1.23  Abstraction          : 0.02
% 2.36/1.23  MUC search           : 0.00
% 2.36/1.23  Cooper               : 0.00
% 2.36/1.23  Total                : 0.56
% 2.36/1.24  Index Insertion      : 0.00
% 2.36/1.24  Index Deletion       : 0.00
% 2.36/1.24  Index Matching       : 0.00
% 2.36/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
