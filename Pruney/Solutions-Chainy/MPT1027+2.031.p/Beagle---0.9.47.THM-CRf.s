%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:46 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 587 expanded)
%              Number of leaves         :   23 ( 201 expanded)
%              Depth                    :   12
%              Number of atoms          :  105 (1347 expanded)
%              Number of equality atoms :   46 ( 319 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_67,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30])).

tff(c_32,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_114,plain,(
    ! [B_34,C_35,A_36] :
      ( k1_xboole_0 = B_34
      | v1_funct_2(C_35,A_36,B_34)
      | k1_relset_1(A_36,B_34,C_35) != A_36
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_117,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_114])).

tff(c_126,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_117])).

tff(c_127,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_126])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_139,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_6])).

tff(c_12,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_137,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_127,c_12])).

tff(c_92,plain,(
    ! [C_22,B_23,A_24] :
      ( ~ v1_xboole_0(C_22)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(C_22))
      | ~ r2_hidden(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_95,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_24,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_92])).

tff(c_96,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_157,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_96])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_157])).

tff(c_163,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_164,plain,(
    ! [A_39] : ~ r2_hidden(A_39,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_169,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_164])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_173,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_169,c_8])).

tff(c_191,plain,(
    ! [A_41] :
      ( A_41 = '#skF_4'
      | ~ v1_xboole_0(A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_8])).

tff(c_198,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_163,c_191])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( k1_xboole_0 = B_7
      | k1_xboole_0 = A_6
      | k2_zfmisc_1(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_231,plain,(
    ! [B_44,A_45] :
      ( B_44 = '#skF_4'
      | A_45 = '#skF_4'
      | k2_zfmisc_1(A_45,B_44) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_173,c_173,c_10])).

tff(c_241,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_231])).

tff(c_246,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_248,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_246,c_32])).

tff(c_217,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_34])).

tff(c_14,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [C_13,B_12] :
      ( v1_funct_2(C_13,k1_xboole_0,B_12)
      | k1_relset_1(k1_xboole_0,B_12,C_13) != k1_xboole_0
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ! [C_13,B_12] :
      ( v1_funct_2(C_13,k1_xboole_0,B_12)
      | k1_relset_1(k1_xboole_0,B_12,C_13) != k1_xboole_0
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_22])).

tff(c_277,plain,(
    ! [C_50,B_51] :
      ( v1_funct_2(C_50,'#skF_4',B_51)
      | k1_relset_1('#skF_4',B_51,C_50) != '#skF_4'
      | ~ m1_subset_1(C_50,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_173,c_173,c_173,c_40])).

tff(c_281,plain,(
    ! [B_52] :
      ( v1_funct_2('#skF_4','#skF_4',B_52)
      | k1_relset_1('#skF_4',B_52,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_217,c_277])).

tff(c_249,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_38])).

tff(c_289,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_281,c_249])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_289])).

tff(c_302,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_18,plain,(
    ! [A_11] :
      ( v1_funct_2(k1_xboole_0,A_11,k1_xboole_0)
      | k1_xboole_0 = A_11
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_11,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_42,plain,(
    ! [A_11] :
      ( v1_funct_2(k1_xboole_0,A_11,k1_xboole_0)
      | k1_xboole_0 = A_11
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18])).

tff(c_229,plain,(
    ! [A_11] :
      ( v1_funct_2('#skF_4',A_11,'#skF_4')
      | A_11 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_173,c_173,c_173,c_173,c_173,c_42])).

tff(c_301,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_313,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_38])).

tff(c_321,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_229,c_313])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_302,c_321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.23  
% 2.04/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.23  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.04/1.23  
% 2.04/1.23  %Foreground sorts:
% 2.04/1.23  
% 2.04/1.23  
% 2.04/1.23  %Background operators:
% 2.04/1.23  
% 2.04/1.23  
% 2.04/1.23  %Foreground operators:
% 2.04/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.04/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.04/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.04/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.04/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.23  
% 2.15/1.25  tff(f_80, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 2.15/1.25  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.15/1.25  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.15/1.25  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.15/1.25  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.15/1.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.15/1.25  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.15/1.25  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.15/1.25  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.15/1.25  tff(c_30, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.15/1.25  tff(c_38, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30])).
% 2.15/1.25  tff(c_32, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.15/1.25  tff(c_114, plain, (![B_34, C_35, A_36]: (k1_xboole_0=B_34 | v1_funct_2(C_35, A_36, B_34) | k1_relset_1(A_36, B_34, C_35)!=A_36 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_34))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.15/1.25  tff(c_117, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_34, c_114])).
% 2.15/1.25  tff(c_126, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_117])).
% 2.15/1.25  tff(c_127, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_38, c_126])).
% 2.15/1.25  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.15/1.25  tff(c_139, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_6])).
% 2.15/1.25  tff(c_12, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.15/1.25  tff(c_137, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_127, c_12])).
% 2.15/1.25  tff(c_92, plain, (![C_22, B_23, A_24]: (~v1_xboole_0(C_22) | ~m1_subset_1(B_23, k1_zfmisc_1(C_22)) | ~r2_hidden(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.25  tff(c_95, plain, (![A_24]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_24, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_92])).
% 2.15/1.25  tff(c_96, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_95])).
% 2.15/1.25  tff(c_157, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_96])).
% 2.15/1.25  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_157])).
% 2.15/1.25  tff(c_163, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_95])).
% 2.15/1.25  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.25  tff(c_164, plain, (![A_39]: (~r2_hidden(A_39, '#skF_4'))), inference(splitRight, [status(thm)], [c_95])).
% 2.15/1.25  tff(c_169, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_164])).
% 2.15/1.25  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.15/1.25  tff(c_173, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_169, c_8])).
% 2.15/1.25  tff(c_191, plain, (![A_41]: (A_41='#skF_4' | ~v1_xboole_0(A_41))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_8])).
% 2.15/1.25  tff(c_198, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_163, c_191])).
% 2.15/1.25  tff(c_10, plain, (![B_7, A_6]: (k1_xboole_0=B_7 | k1_xboole_0=A_6 | k2_zfmisc_1(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.15/1.25  tff(c_231, plain, (![B_44, A_45]: (B_44='#skF_4' | A_45='#skF_4' | k2_zfmisc_1(A_45, B_44)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_173, c_173, c_10])).
% 2.15/1.25  tff(c_241, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_198, c_231])).
% 2.15/1.25  tff(c_246, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_241])).
% 2.15/1.25  tff(c_248, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_246, c_246, c_32])).
% 2.15/1.25  tff(c_217, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_34])).
% 2.15/1.25  tff(c_14, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.15/1.25  tff(c_22, plain, (![C_13, B_12]: (v1_funct_2(C_13, k1_xboole_0, B_12) | k1_relset_1(k1_xboole_0, B_12, C_13)!=k1_xboole_0 | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_12))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.15/1.25  tff(c_40, plain, (![C_13, B_12]: (v1_funct_2(C_13, k1_xboole_0, B_12) | k1_relset_1(k1_xboole_0, B_12, C_13)!=k1_xboole_0 | ~m1_subset_1(C_13, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_22])).
% 2.15/1.25  tff(c_277, plain, (![C_50, B_51]: (v1_funct_2(C_50, '#skF_4', B_51) | k1_relset_1('#skF_4', B_51, C_50)!='#skF_4' | ~m1_subset_1(C_50, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_173, c_173, c_173, c_40])).
% 2.15/1.25  tff(c_281, plain, (![B_52]: (v1_funct_2('#skF_4', '#skF_4', B_52) | k1_relset_1('#skF_4', B_52, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_217, c_277])).
% 2.15/1.25  tff(c_249, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_38])).
% 2.15/1.25  tff(c_289, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_281, c_249])).
% 2.15/1.25  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_248, c_289])).
% 2.15/1.25  tff(c_302, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_241])).
% 2.15/1.25  tff(c_18, plain, (![A_11]: (v1_funct_2(k1_xboole_0, A_11, k1_xboole_0) | k1_xboole_0=A_11 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_11, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.15/1.25  tff(c_42, plain, (![A_11]: (v1_funct_2(k1_xboole_0, A_11, k1_xboole_0) | k1_xboole_0=A_11 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18])).
% 2.15/1.25  tff(c_229, plain, (![A_11]: (v1_funct_2('#skF_4', A_11, '#skF_4') | A_11='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_173, c_173, c_173, c_173, c_173, c_42])).
% 2.15/1.25  tff(c_301, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_241])).
% 2.15/1.25  tff(c_313, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_38])).
% 2.15/1.25  tff(c_321, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_229, c_313])).
% 2.15/1.25  tff(c_325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_302, c_321])).
% 2.15/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.25  
% 2.15/1.25  Inference rules
% 2.15/1.25  ----------------------
% 2.15/1.25  #Ref     : 0
% 2.15/1.25  #Sup     : 56
% 2.15/1.25  #Fact    : 0
% 2.15/1.25  #Define  : 0
% 2.15/1.25  #Split   : 3
% 2.15/1.25  #Chain   : 0
% 2.15/1.25  #Close   : 0
% 2.15/1.25  
% 2.15/1.25  Ordering : KBO
% 2.15/1.25  
% 2.15/1.25  Simplification rules
% 2.15/1.25  ----------------------
% 2.15/1.25  #Subsume      : 4
% 2.15/1.25  #Demod        : 87
% 2.15/1.25  #Tautology    : 47
% 2.15/1.25  #SimpNegUnit  : 2
% 2.15/1.25  #BackRed      : 26
% 2.15/1.25  
% 2.15/1.25  #Partial instantiations: 0
% 2.15/1.25  #Strategies tried      : 1
% 2.15/1.25  
% 2.15/1.25  Timing (in seconds)
% 2.15/1.25  ----------------------
% 2.15/1.25  Preprocessing        : 0.29
% 2.15/1.25  Parsing              : 0.16
% 2.15/1.25  CNF conversion       : 0.02
% 2.15/1.25  Main loop            : 0.21
% 2.15/1.25  Inferencing          : 0.07
% 2.15/1.25  Reduction            : 0.06
% 2.15/1.25  Demodulation         : 0.05
% 2.15/1.25  BG Simplification    : 0.01
% 2.15/1.25  Subsumption          : 0.04
% 2.15/1.25  Abstraction          : 0.01
% 2.15/1.25  MUC search           : 0.00
% 2.15/1.25  Cooper               : 0.00
% 2.15/1.25  Total                : 0.53
% 2.15/1.25  Index Insertion      : 0.00
% 2.15/1.25  Index Deletion       : 0.00
% 2.15/1.25  Index Matching       : 0.00
% 2.15/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
