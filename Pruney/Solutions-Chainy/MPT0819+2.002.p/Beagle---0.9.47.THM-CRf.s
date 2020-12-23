%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:58 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   54 (  93 expanded)
%              Number of leaves         :   24 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 178 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_27,plain,(
    ! [C_17,A_18,B_19] :
      ( v1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_31,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_27])).

tff(c_64,plain,(
    ! [C_32,B_33,A_34] :
      ( v5_relat_1(C_32,B_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_34,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_68,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_50,plain,(
    ! [B_27,A_28] :
      ( r1_tarski(k2_relat_1(B_27),A_28)
      | ~ v5_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_33,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_tarski(A_22,C_23)
      | ~ r1_tarski(B_24,C_23)
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_22] :
      ( r1_tarski(A_22,'#skF_4')
      | ~ r1_tarski(A_22,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_33])).

tff(c_57,plain,(
    ! [B_27] :
      ( r1_tarski(k2_relat_1(B_27),'#skF_4')
      | ~ v5_relat_1(B_27,'#skF_3')
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_50,c_38])).

tff(c_59,plain,(
    ! [C_29,A_30,B_31] :
      ( v4_relat_1(C_29,A_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_63,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_59])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_41,plain,(
    ! [A_26] :
      ( r1_tarski(A_26,'#skF_2')
      | ~ r1_tarski(A_26,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_33])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( v4_relat_1(B_5,A_4)
      | ~ r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_114,plain,(
    ! [B_43] :
      ( v4_relat_1(B_43,'#skF_2')
      | ~ v1_relat_1(B_43)
      | ~ r1_tarski(k1_relat_1(B_43),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_41,c_4])).

tff(c_119,plain,(
    ! [B_5] :
      ( v4_relat_1(B_5,'#skF_2')
      | ~ v4_relat_1(B_5,'#skF_1')
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_141,plain,(
    ! [C_47,A_48,B_49] :
      ( m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ r1_tarski(k2_relat_1(C_47),B_49)
      | ~ r1_tarski(k1_relat_1(C_47),A_48)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_153,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_141,c_20])).

tff(c_159,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_153])).

tff(c_161,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_175,plain,
    ( ~ v4_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_161])).

tff(c_181,plain,(
    ~ v4_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_175])).

tff(c_185,plain,
    ( ~ v4_relat_1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_119,c_181])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_63,c_185])).

tff(c_190,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_194,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_57,c_190])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_68,c_194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:21:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.20  
% 2.02/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.20  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.02/1.20  
% 2.02/1.20  %Foreground sorts:
% 2.02/1.20  
% 2.02/1.20  
% 2.02/1.20  %Background operators:
% 2.02/1.20  
% 2.02/1.20  
% 2.02/1.20  %Foreground operators:
% 2.02/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.20  tff('#skF_5', type, '#skF_5': $i).
% 2.02/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.02/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.20  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.02/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.20  
% 2.02/1.22  tff(f_70, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_relset_1)).
% 2.02/1.22  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.02/1.22  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.02/1.22  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.02/1.22  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.02/1.22  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.02/1.22  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.02/1.22  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.02/1.22  tff(c_27, plain, (![C_17, A_18, B_19]: (v1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.02/1.22  tff(c_31, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_27])).
% 2.02/1.22  tff(c_64, plain, (![C_32, B_33, A_34]: (v5_relat_1(C_32, B_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_34, B_33))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.02/1.22  tff(c_68, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_64])).
% 2.02/1.22  tff(c_50, plain, (![B_27, A_28]: (r1_tarski(k2_relat_1(B_27), A_28) | ~v5_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.02/1.22  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.02/1.22  tff(c_33, plain, (![A_22, C_23, B_24]: (r1_tarski(A_22, C_23) | ~r1_tarski(B_24, C_23) | ~r1_tarski(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.22  tff(c_38, plain, (![A_22]: (r1_tarski(A_22, '#skF_4') | ~r1_tarski(A_22, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_33])).
% 2.02/1.22  tff(c_57, plain, (![B_27]: (r1_tarski(k2_relat_1(B_27), '#skF_4') | ~v5_relat_1(B_27, '#skF_3') | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_50, c_38])).
% 2.02/1.22  tff(c_59, plain, (![C_29, A_30, B_31]: (v4_relat_1(C_29, A_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.02/1.22  tff(c_63, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_59])).
% 2.02/1.22  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.22  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.02/1.22  tff(c_41, plain, (![A_26]: (r1_tarski(A_26, '#skF_2') | ~r1_tarski(A_26, '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_33])).
% 2.02/1.22  tff(c_4, plain, (![B_5, A_4]: (v4_relat_1(B_5, A_4) | ~r1_tarski(k1_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.22  tff(c_114, plain, (![B_43]: (v4_relat_1(B_43, '#skF_2') | ~v1_relat_1(B_43) | ~r1_tarski(k1_relat_1(B_43), '#skF_1'))), inference(resolution, [status(thm)], [c_41, c_4])).
% 2.02/1.22  tff(c_119, plain, (![B_5]: (v4_relat_1(B_5, '#skF_2') | ~v4_relat_1(B_5, '#skF_1') | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_114])).
% 2.02/1.22  tff(c_141, plain, (![C_47, A_48, B_49]: (m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~r1_tarski(k2_relat_1(C_47), B_49) | ~r1_tarski(k1_relat_1(C_47), A_48) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.02/1.22  tff(c_20, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.02/1.22  tff(c_153, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_141, c_20])).
% 2.02/1.22  tff(c_159, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_31, c_153])).
% 2.02/1.22  tff(c_161, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_159])).
% 2.02/1.22  tff(c_175, plain, (~v4_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6, c_161])).
% 2.02/1.22  tff(c_181, plain, (~v4_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_31, c_175])).
% 2.02/1.22  tff(c_185, plain, (~v4_relat_1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_119, c_181])).
% 2.02/1.22  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31, c_63, c_185])).
% 2.02/1.22  tff(c_190, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_159])).
% 2.02/1.22  tff(c_194, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_57, c_190])).
% 2.02/1.22  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31, c_68, c_194])).
% 2.02/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.22  
% 2.02/1.22  Inference rules
% 2.02/1.22  ----------------------
% 2.02/1.22  #Ref     : 0
% 2.02/1.22  #Sup     : 37
% 2.02/1.22  #Fact    : 0
% 2.02/1.22  #Define  : 0
% 2.02/1.22  #Split   : 2
% 2.02/1.22  #Chain   : 0
% 2.02/1.22  #Close   : 0
% 2.02/1.22  
% 2.02/1.22  Ordering : KBO
% 2.02/1.22  
% 2.02/1.22  Simplification rules
% 2.02/1.22  ----------------------
% 2.02/1.22  #Subsume      : 4
% 2.02/1.22  #Demod        : 8
% 2.02/1.22  #Tautology    : 4
% 2.02/1.22  #SimpNegUnit  : 0
% 2.02/1.22  #BackRed      : 0
% 2.02/1.22  
% 2.02/1.22  #Partial instantiations: 0
% 2.02/1.22  #Strategies tried      : 1
% 2.02/1.22  
% 2.02/1.22  Timing (in seconds)
% 2.02/1.22  ----------------------
% 2.02/1.22  Preprocessing        : 0.27
% 2.02/1.22  Parsing              : 0.16
% 2.02/1.22  CNF conversion       : 0.02
% 2.02/1.22  Main loop            : 0.19
% 2.02/1.22  Inferencing          : 0.08
% 2.02/1.22  Reduction            : 0.05
% 2.02/1.22  Demodulation         : 0.03
% 2.02/1.22  BG Simplification    : 0.01
% 2.02/1.22  Subsumption          : 0.04
% 2.02/1.22  Abstraction          : 0.01
% 2.02/1.22  MUC search           : 0.00
% 2.02/1.22  Cooper               : 0.00
% 2.02/1.22  Total                : 0.49
% 2.02/1.22  Index Insertion      : 0.00
% 2.02/1.22  Index Deletion       : 0.00
% 2.02/1.22  Index Matching       : 0.00
% 2.02/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
