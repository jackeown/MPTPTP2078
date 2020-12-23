%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:47 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 455 expanded)
%              Number of leaves         :   24 ( 163 expanded)
%              Depth                    :   13
%              Number of atoms          :  103 (1254 expanded)
%              Number of equality atoms :   44 ( 341 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(f_63,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_81,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_16,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_1'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34])).

tff(c_36,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_155,plain,(
    ! [B_63,C_64,A_65] :
      ( k1_xboole_0 = B_63
      | v1_funct_2(C_64,A_65,B_63)
      | k1_relset_1(A_65,B_63,C_64) != A_65
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_158,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_155])).

tff(c_171,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_158])).

tff(c_172,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_171])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_191,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_2])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_190,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_172,c_6])).

tff(c_88,plain,(
    ! [C_34,B_35,A_36] :
      ( ~ v1_xboole_0(C_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(C_34))
      | ~ r2_hidden(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_36,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_88])).

tff(c_103,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_205,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_103])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_205])).

tff(c_212,plain,(
    ! [A_70] : ~ r2_hidden(A_70,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_217,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16,c_212])).

tff(c_10,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [A_24] :
      ( v1_funct_2(k1_xboole_0,A_24,k1_xboole_0)
      | k1_xboole_0 = A_24
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_24,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    ! [A_24] :
      ( v1_funct_2(k1_xboole_0,A_24,k1_xboole_0)
      | k1_xboole_0 = A_24 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22])).

tff(c_219,plain,(
    ! [A_24] :
      ( v1_funct_2('#skF_4',A_24,'#skF_4')
      | A_24 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_217,c_217,c_44])).

tff(c_223,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_10])).

tff(c_28,plain,(
    ! [B_25,C_26,A_24] :
      ( k1_xboole_0 = B_25
      | v1_funct_2(C_26,A_24,B_25)
      | k1_relset_1(A_24,B_25,C_26) != A_24
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_310,plain,(
    ! [B_99,C_100,A_101] :
      ( B_99 = '#skF_4'
      | v1_funct_2(C_100,A_101,B_99)
      | k1_relset_1(A_101,B_99,C_100) != A_101
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_99))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_28])).

tff(c_331,plain,(
    ! [B_103,A_104] :
      ( B_103 = '#skF_4'
      | v1_funct_2('#skF_4',A_104,B_103)
      | k1_relset_1(A_104,B_103,'#skF_4') != A_104 ) ),
    inference(resolution,[status(thm)],[c_223,c_310])).

tff(c_337,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_331,c_42])).

tff(c_344,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_337])).

tff(c_347,plain,(
    ~ v1_funct_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_42])).

tff(c_361,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_219,c_347])).

tff(c_346,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_36])).

tff(c_401,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_361,c_346])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [C_26,B_25] :
      ( v1_funct_2(C_26,k1_xboole_0,B_25)
      | k1_relset_1(k1_xboole_0,B_25,C_26) != k1_xboole_0
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_46,plain,(
    ! [C_26,B_25] :
      ( v1_funct_2(C_26,k1_xboole_0,B_25)
      | k1_relset_1(k1_xboole_0,B_25,C_26) != k1_xboole_0
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_26])).

tff(c_304,plain,(
    ! [C_97,B_98] :
      ( v1_funct_2(C_97,'#skF_4',B_98)
      | k1_relset_1('#skF_4',B_98,C_97) != '#skF_4'
      | ~ m1_subset_1(C_97,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_217,c_217,c_217,c_46])).

tff(c_308,plain,(
    ! [B_98] :
      ( v1_funct_2('#skF_4','#skF_4',B_98)
      | k1_relset_1('#skF_4',B_98,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_223,c_304])).

tff(c_362,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_347])).

tff(c_398,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_308,c_362])).

tff(c_407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:28:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.28  
% 2.36/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.36/1.29  
% 2.36/1.29  %Foreground sorts:
% 2.36/1.29  
% 2.36/1.29  
% 2.36/1.29  %Background operators:
% 2.36/1.29  
% 2.36/1.29  
% 2.36/1.29  %Foreground operators:
% 2.36/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.36/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.36/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.29  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.36/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.36/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.36/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.29  
% 2.36/1.30  tff(f_63, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 2.36/1.30  tff(f_94, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 2.36/1.30  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.36/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.36/1.30  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.36/1.30  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.36/1.30  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.36/1.30  tff(c_16, plain, (![A_10]: (r2_hidden('#skF_1'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.36/1.30  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.36/1.30  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.36/1.30  tff(c_34, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.36/1.30  tff(c_42, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34])).
% 2.36/1.30  tff(c_36, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.36/1.30  tff(c_155, plain, (![B_63, C_64, A_65]: (k1_xboole_0=B_63 | v1_funct_2(C_64, A_65, B_63) | k1_relset_1(A_65, B_63, C_64)!=A_65 | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_63))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.36/1.30  tff(c_158, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_38, c_155])).
% 2.36/1.30  tff(c_171, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_158])).
% 2.36/1.30  tff(c_172, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_42, c_171])).
% 2.36/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.36/1.30  tff(c_191, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_2])).
% 2.36/1.30  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.36/1.30  tff(c_190, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_172, c_6])).
% 2.36/1.30  tff(c_88, plain, (![C_34, B_35, A_36]: (~v1_xboole_0(C_34) | ~m1_subset_1(B_35, k1_zfmisc_1(C_34)) | ~r2_hidden(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.36/1.30  tff(c_93, plain, (![A_36]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_36, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_88])).
% 2.36/1.30  tff(c_103, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_93])).
% 2.36/1.30  tff(c_205, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_103])).
% 2.36/1.30  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_191, c_205])).
% 2.36/1.30  tff(c_212, plain, (![A_70]: (~r2_hidden(A_70, '#skF_4'))), inference(splitRight, [status(thm)], [c_93])).
% 2.36/1.30  tff(c_217, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_16, c_212])).
% 2.36/1.30  tff(c_10, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.36/1.30  tff(c_22, plain, (![A_24]: (v1_funct_2(k1_xboole_0, A_24, k1_xboole_0) | k1_xboole_0=A_24 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_24, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.36/1.30  tff(c_44, plain, (![A_24]: (v1_funct_2(k1_xboole_0, A_24, k1_xboole_0) | k1_xboole_0=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22])).
% 2.36/1.30  tff(c_219, plain, (![A_24]: (v1_funct_2('#skF_4', A_24, '#skF_4') | A_24='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_217, c_217, c_44])).
% 2.36/1.30  tff(c_223, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_10])).
% 2.36/1.30  tff(c_28, plain, (![B_25, C_26, A_24]: (k1_xboole_0=B_25 | v1_funct_2(C_26, A_24, B_25) | k1_relset_1(A_24, B_25, C_26)!=A_24 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.36/1.30  tff(c_310, plain, (![B_99, C_100, A_101]: (B_99='#skF_4' | v1_funct_2(C_100, A_101, B_99) | k1_relset_1(A_101, B_99, C_100)!=A_101 | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_99))))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_28])).
% 2.36/1.30  tff(c_331, plain, (![B_103, A_104]: (B_103='#skF_4' | v1_funct_2('#skF_4', A_104, B_103) | k1_relset_1(A_104, B_103, '#skF_4')!=A_104)), inference(resolution, [status(thm)], [c_223, c_310])).
% 2.36/1.30  tff(c_337, plain, ('#skF_3'='#skF_4' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_331, c_42])).
% 2.36/1.30  tff(c_344, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_337])).
% 2.36/1.30  tff(c_347, plain, (~v1_funct_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_344, c_42])).
% 2.36/1.30  tff(c_361, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_219, c_347])).
% 2.36/1.30  tff(c_346, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_344, c_36])).
% 2.36/1.30  tff(c_401, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_361, c_361, c_346])).
% 2.36/1.30  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.36/1.30  tff(c_26, plain, (![C_26, B_25]: (v1_funct_2(C_26, k1_xboole_0, B_25) | k1_relset_1(k1_xboole_0, B_25, C_26)!=k1_xboole_0 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_25))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.36/1.30  tff(c_46, plain, (![C_26, B_25]: (v1_funct_2(C_26, k1_xboole_0, B_25) | k1_relset_1(k1_xboole_0, B_25, C_26)!=k1_xboole_0 | ~m1_subset_1(C_26, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_26])).
% 2.36/1.30  tff(c_304, plain, (![C_97, B_98]: (v1_funct_2(C_97, '#skF_4', B_98) | k1_relset_1('#skF_4', B_98, C_97)!='#skF_4' | ~m1_subset_1(C_97, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_217, c_217, c_217, c_46])).
% 2.36/1.30  tff(c_308, plain, (![B_98]: (v1_funct_2('#skF_4', '#skF_4', B_98) | k1_relset_1('#skF_4', B_98, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_223, c_304])).
% 2.36/1.30  tff(c_362, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_361, c_347])).
% 2.36/1.30  tff(c_398, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_308, c_362])).
% 2.36/1.30  tff(c_407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_401, c_398])).
% 2.36/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.30  
% 2.36/1.30  Inference rules
% 2.36/1.30  ----------------------
% 2.36/1.30  #Ref     : 0
% 2.36/1.30  #Sup     : 68
% 2.36/1.30  #Fact    : 0
% 2.36/1.30  #Define  : 0
% 2.36/1.30  #Split   : 2
% 2.36/1.30  #Chain   : 0
% 2.36/1.30  #Close   : 0
% 2.36/1.30  
% 2.36/1.30  Ordering : KBO
% 2.36/1.30  
% 2.36/1.30  Simplification rules
% 2.36/1.30  ----------------------
% 2.36/1.30  #Subsume      : 8
% 2.36/1.30  #Demod        : 99
% 2.36/1.30  #Tautology    : 47
% 2.36/1.30  #SimpNegUnit  : 1
% 2.36/1.30  #BackRed      : 32
% 2.36/1.30  
% 2.36/1.30  #Partial instantiations: 0
% 2.36/1.30  #Strategies tried      : 1
% 2.36/1.30  
% 2.36/1.30  Timing (in seconds)
% 2.36/1.30  ----------------------
% 2.36/1.30  Preprocessing        : 0.30
% 2.36/1.30  Parsing              : 0.17
% 2.36/1.30  CNF conversion       : 0.02
% 2.36/1.30  Main loop            : 0.24
% 2.36/1.30  Inferencing          : 0.08
% 2.36/1.30  Reduction            : 0.07
% 2.36/1.31  Demodulation         : 0.05
% 2.36/1.31  BG Simplification    : 0.02
% 2.36/1.31  Subsumption          : 0.04
% 2.36/1.31  Abstraction          : 0.01
% 2.36/1.31  MUC search           : 0.00
% 2.36/1.31  Cooper               : 0.00
% 2.36/1.31  Total                : 0.57
% 2.36/1.31  Index Insertion      : 0.00
% 2.36/1.31  Index Deletion       : 0.00
% 2.36/1.31  Index Matching       : 0.00
% 2.36/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
