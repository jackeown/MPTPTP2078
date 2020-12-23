%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:56 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 101 expanded)
%              Number of leaves         :   27 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :   86 ( 285 expanded)
%              Number of equality atoms :   11 (  21 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,A,B)
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                   => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_38,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_28,plain,(
    ! [D_24,C_23,A_21,B_22] :
      ( r2_hidden(k1_funct_1(D_24,C_23),k2_relset_1(A_21,B_22,D_24))
      | k1_xboole_0 = B_22
      | ~ r2_hidden(C_23,A_21)
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(D_24,A_21,B_22)
      | ~ v1_funct_1(D_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_123,plain,(
    ! [A_57,B_58,C_59,D_60] :
      ( k3_funct_2(A_57,B_58,C_59,D_60) = k1_funct_1(C_59,D_60)
      | ~ m1_subset_1(D_60,A_57)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ v1_funct_1(C_59)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_127,plain,(
    ! [B_58,C_59] :
      ( k3_funct_2('#skF_1',B_58,C_59,'#skF_3') = k1_funct_1(C_59,'#skF_3')
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_58)))
      | ~ v1_funct_2(C_59,'#skF_1',B_58)
      | ~ v1_funct_1(C_59)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_123])).

tff(c_132,plain,(
    ! [B_61,C_62] :
      ( k3_funct_2('#skF_1',B_61,C_62,'#skF_3') = k1_funct_1(C_62,'#skF_3')
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_61)))
      | ~ v1_funct_2(C_62,'#skF_1',B_61)
      | ~ v1_funct_1(C_62) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_127])).

tff(c_135,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_132])).

tff(c_142,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_135])).

tff(c_30,plain,(
    ~ r2_hidden(k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_144,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_30])).

tff(c_151,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_144])).

tff(c_157,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_151])).

tff(c_159,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_162,plain,
    ( v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_159])).

tff(c_165,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_162])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_165])).

tff(c_168,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    ! [B_47,A_48] :
      ( ~ r1_xboole_0(B_47,A_48)
      | ~ r1_tarski(B_47,A_48)
      | v1_xboole_0(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [A_49] :
      ( ~ r1_tarski(A_49,k1_xboole_0)
      | v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_4,c_86])).

tff(c_96,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_91])).

tff(c_172,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_96])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:25:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.24  
% 2.20/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.24  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.20/1.24  
% 2.20/1.24  %Foreground sorts:
% 2.20/1.24  
% 2.20/1.24  
% 2.20/1.24  %Background operators:
% 2.20/1.24  
% 2.20/1.24  
% 2.20/1.24  %Foreground operators:
% 2.20/1.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.20/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.20/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.20/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.20/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.20/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.20/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.24  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.20/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.24  
% 2.20/1.26  tff(f_125, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 2.20/1.26  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.20/1.26  tff(f_105, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.20/1.26  tff(f_93, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.20/1.26  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.20/1.26  tff(f_29, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.20/1.26  tff(f_37, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.20/1.26  tff(c_40, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.20/1.26  tff(c_42, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.20/1.26  tff(c_38, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.20/1.26  tff(c_16, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.20/1.26  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.20/1.26  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.20/1.26  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.20/1.26  tff(c_28, plain, (![D_24, C_23, A_21, B_22]: (r2_hidden(k1_funct_1(D_24, C_23), k2_relset_1(A_21, B_22, D_24)) | k1_xboole_0=B_22 | ~r2_hidden(C_23, A_21) | ~m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(D_24, A_21, B_22) | ~v1_funct_1(D_24))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.20/1.26  tff(c_123, plain, (![A_57, B_58, C_59, D_60]: (k3_funct_2(A_57, B_58, C_59, D_60)=k1_funct_1(C_59, D_60) | ~m1_subset_1(D_60, A_57) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_2(C_59, A_57, B_58) | ~v1_funct_1(C_59) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.20/1.26  tff(c_127, plain, (![B_58, C_59]: (k3_funct_2('#skF_1', B_58, C_59, '#skF_3')=k1_funct_1(C_59, '#skF_3') | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_58))) | ~v1_funct_2(C_59, '#skF_1', B_58) | ~v1_funct_1(C_59) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_123])).
% 2.20/1.26  tff(c_132, plain, (![B_61, C_62]: (k3_funct_2('#skF_1', B_61, C_62, '#skF_3')=k1_funct_1(C_62, '#skF_3') | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_61))) | ~v1_funct_2(C_62, '#skF_1', B_61) | ~v1_funct_1(C_62))), inference(negUnitSimplification, [status(thm)], [c_42, c_127])).
% 2.20/1.26  tff(c_135, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_132])).
% 2.20/1.26  tff(c_142, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_135])).
% 2.20/1.26  tff(c_30, plain, (~r2_hidden(k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.20/1.26  tff(c_144, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_30])).
% 2.20/1.26  tff(c_151, plain, (k1_xboole_0='#skF_2' | ~r2_hidden('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_144])).
% 2.20/1.26  tff(c_157, plain, (k1_xboole_0='#skF_2' | ~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_151])).
% 2.20/1.26  tff(c_159, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_157])).
% 2.20/1.26  tff(c_162, plain, (v1_xboole_0('#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_16, c_159])).
% 2.20/1.26  tff(c_165, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_162])).
% 2.20/1.26  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_165])).
% 2.20/1.26  tff(c_168, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_157])).
% 2.20/1.26  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.20/1.26  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.26  tff(c_86, plain, (![B_47, A_48]: (~r1_xboole_0(B_47, A_48) | ~r1_tarski(B_47, A_48) | v1_xboole_0(B_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.26  tff(c_91, plain, (![A_49]: (~r1_tarski(A_49, k1_xboole_0) | v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_4, c_86])).
% 2.20/1.26  tff(c_96, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_91])).
% 2.20/1.26  tff(c_172, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_96])).
% 2.20/1.26  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_172])).
% 2.20/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.26  
% 2.20/1.26  Inference rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Ref     : 0
% 2.20/1.26  #Sup     : 25
% 2.20/1.26  #Fact    : 0
% 2.20/1.26  #Define  : 0
% 2.20/1.26  #Split   : 3
% 2.20/1.26  #Chain   : 0
% 2.20/1.26  #Close   : 0
% 2.20/1.26  
% 2.20/1.26  Ordering : KBO
% 2.20/1.26  
% 2.20/1.26  Simplification rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Subsume      : 0
% 2.20/1.26  #Demod        : 25
% 2.20/1.26  #Tautology    : 14
% 2.20/1.26  #SimpNegUnit  : 4
% 2.20/1.26  #BackRed      : 11
% 2.20/1.26  
% 2.20/1.26  #Partial instantiations: 0
% 2.20/1.26  #Strategies tried      : 1
% 2.20/1.26  
% 2.20/1.26  Timing (in seconds)
% 2.20/1.26  ----------------------
% 2.20/1.26  Preprocessing        : 0.32
% 2.20/1.26  Parsing              : 0.17
% 2.20/1.26  CNF conversion       : 0.02
% 2.20/1.26  Main loop            : 0.17
% 2.20/1.26  Inferencing          : 0.06
% 2.20/1.26  Reduction            : 0.06
% 2.20/1.26  Demodulation         : 0.04
% 2.20/1.26  BG Simplification    : 0.01
% 2.20/1.26  Subsumption          : 0.03
% 2.20/1.26  Abstraction          : 0.01
% 2.20/1.26  MUC search           : 0.00
% 2.20/1.26  Cooper               : 0.00
% 2.20/1.26  Total                : 0.52
% 2.20/1.26  Index Insertion      : 0.00
% 2.20/1.26  Index Deletion       : 0.00
% 2.20/1.26  Index Matching       : 0.00
% 2.20/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
