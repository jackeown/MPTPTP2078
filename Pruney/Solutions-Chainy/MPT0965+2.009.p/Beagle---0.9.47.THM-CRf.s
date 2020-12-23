%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:01 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   63 (  81 expanded)
%              Number of leaves         :   33 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 166 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
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

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_78,plain,(
    ! [C_46,B_47,A_48] :
      ( v5_relat_1(C_46,B_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_48,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_82,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_78])).

tff(c_40,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_63,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_67,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_63])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_121,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_125,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_121])).

tff(c_150,plain,(
    ! [B_97,A_98,C_99] :
      ( k1_xboole_0 = B_97
      | k1_relset_1(A_98,B_97,C_99) = A_98
      | ~ v1_funct_2(C_99,A_98,B_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_153,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_150])).

tff(c_156,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_125,c_153])).

tff(c_157,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_156])).

tff(c_8,plain,(
    ! [C_9,B_8,A_7] :
      ( m1_subset_1(k1_funct_1(C_9,B_8),A_7)
      | ~ r2_hidden(B_8,k1_relat_1(C_9))
      | ~ v1_funct_1(C_9)
      | ~ v5_relat_1(C_9,A_7)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_161,plain,(
    ! [B_8,A_7] :
      ( m1_subset_1(k1_funct_1('#skF_6',B_8),A_7)
      | ~ r2_hidden(B_8,'#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_7)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_8])).

tff(c_171,plain,(
    ! [B_100,A_101] :
      ( m1_subset_1(k1_funct_1('#skF_6',B_100),A_101)
      | ~ r2_hidden(B_100,'#skF_3')
      | ~ v5_relat_1('#skF_6',A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_46,c_161])).

tff(c_68,plain,(
    ! [A_44,B_45] :
      ( r2_hidden(A_44,B_45)
      | v1_xboole_0(B_45)
      | ~ m1_subset_1(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_75,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_36])).

tff(c_77,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_198,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_171,c_77])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_40,c_198])).

tff(c_217,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_52,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_2'(A_38),A_38)
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(A_38)
      | k1_xboole_0 = A_38 ) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_221,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_217,c_56])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.37  
% 2.32/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.32/1.37  
% 2.32/1.37  %Foreground sorts:
% 2.32/1.37  
% 2.32/1.37  
% 2.32/1.37  %Background operators:
% 2.32/1.37  
% 2.32/1.37  
% 2.32/1.37  %Foreground operators:
% 2.32/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.32/1.37  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.32/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.32/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.37  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.32/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.32/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.32/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.32/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.32/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.32/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.32/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.32/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.37  
% 2.32/1.38  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.32/1.38  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.32/1.38  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.32/1.38  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.32/1.38  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.32/1.38  tff(f_47, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 2.32/1.38  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.32/1.38  tff(f_77, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 2.32/1.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.32/1.38  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.38  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.38  tff(c_78, plain, (![C_46, B_47, A_48]: (v5_relat_1(C_46, B_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_48, B_47))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.32/1.38  tff(c_82, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_78])).
% 2.32/1.38  tff(c_40, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.38  tff(c_63, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.32/1.38  tff(c_67, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_63])).
% 2.32/1.38  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.38  tff(c_44, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.38  tff(c_121, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.32/1.38  tff(c_125, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_121])).
% 2.32/1.38  tff(c_150, plain, (![B_97, A_98, C_99]: (k1_xboole_0=B_97 | k1_relset_1(A_98, B_97, C_99)=A_98 | ~v1_funct_2(C_99, A_98, B_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.32/1.38  tff(c_153, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_150])).
% 2.32/1.38  tff(c_156, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_125, c_153])).
% 2.32/1.38  tff(c_157, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_38, c_156])).
% 2.32/1.38  tff(c_8, plain, (![C_9, B_8, A_7]: (m1_subset_1(k1_funct_1(C_9, B_8), A_7) | ~r2_hidden(B_8, k1_relat_1(C_9)) | ~v1_funct_1(C_9) | ~v5_relat_1(C_9, A_7) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.32/1.38  tff(c_161, plain, (![B_8, A_7]: (m1_subset_1(k1_funct_1('#skF_6', B_8), A_7) | ~r2_hidden(B_8, '#skF_3') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_7) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_157, c_8])).
% 2.32/1.38  tff(c_171, plain, (![B_100, A_101]: (m1_subset_1(k1_funct_1('#skF_6', B_100), A_101) | ~r2_hidden(B_100, '#skF_3') | ~v5_relat_1('#skF_6', A_101))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_46, c_161])).
% 2.32/1.38  tff(c_68, plain, (![A_44, B_45]: (r2_hidden(A_44, B_45) | v1_xboole_0(B_45) | ~m1_subset_1(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.32/1.38  tff(c_36, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.38  tff(c_75, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_68, c_36])).
% 2.32/1.38  tff(c_77, plain, (~m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_75])).
% 2.32/1.38  tff(c_198, plain, (~r2_hidden('#skF_5', '#skF_3') | ~v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_171, c_77])).
% 2.32/1.38  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_40, c_198])).
% 2.32/1.38  tff(c_217, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_75])).
% 2.32/1.38  tff(c_52, plain, (![A_38]: (r2_hidden('#skF_2'(A_38), A_38) | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.32/1.38  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.38  tff(c_56, plain, (![A_38]: (~v1_xboole_0(A_38) | k1_xboole_0=A_38)), inference(resolution, [status(thm)], [c_52, c_2])).
% 2.32/1.38  tff(c_221, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_217, c_56])).
% 2.32/1.38  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_221])).
% 2.32/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.38  
% 2.32/1.38  Inference rules
% 2.32/1.38  ----------------------
% 2.32/1.38  #Ref     : 0
% 2.32/1.38  #Sup     : 38
% 2.32/1.38  #Fact    : 0
% 2.32/1.38  #Define  : 0
% 2.32/1.38  #Split   : 3
% 2.32/1.38  #Chain   : 0
% 2.32/1.38  #Close   : 0
% 2.32/1.38  
% 2.32/1.38  Ordering : KBO
% 2.32/1.38  
% 2.32/1.38  Simplification rules
% 2.32/1.38  ----------------------
% 2.32/1.38  #Subsume      : 0
% 2.32/1.38  #Demod        : 7
% 2.32/1.38  #Tautology    : 8
% 2.32/1.38  #SimpNegUnit  : 2
% 2.32/1.39  #BackRed      : 1
% 2.32/1.39  
% 2.32/1.39  #Partial instantiations: 0
% 2.32/1.39  #Strategies tried      : 1
% 2.32/1.39  
% 2.32/1.39  Timing (in seconds)
% 2.32/1.39  ----------------------
% 2.32/1.39  Preprocessing        : 0.36
% 2.32/1.39  Parsing              : 0.18
% 2.32/1.39  CNF conversion       : 0.03
% 2.32/1.39  Main loop            : 0.19
% 2.32/1.39  Inferencing          : 0.07
% 2.32/1.39  Reduction            : 0.06
% 2.32/1.39  Demodulation         : 0.04
% 2.32/1.39  BG Simplification    : 0.02
% 2.32/1.39  Subsumption          : 0.03
% 2.32/1.39  Abstraction          : 0.01
% 2.32/1.39  MUC search           : 0.00
% 2.32/1.39  Cooper               : 0.00
% 2.32/1.39  Total                : 0.58
% 2.32/1.39  Index Insertion      : 0.00
% 2.32/1.39  Index Deletion       : 0.00
% 2.32/1.39  Index Matching       : 0.00
% 2.32/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
