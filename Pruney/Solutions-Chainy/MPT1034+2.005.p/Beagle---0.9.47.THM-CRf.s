%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:57 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 118 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :    6
%              Number of atoms          :  112 ( 403 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k11_relat_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r1_partfun1(B,C)
             => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_2)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
         => ( ! [D] :
                ( r2_hidden(D,A)
               => k11_relat_1(B,D) = k11_relat_1(C,D) )
           => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_107,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( r2_relset_1(A_42,B_43,C_44,C_44)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    ! [C_46] :
      ( r2_relset_1('#skF_3','#skF_3',C_46,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_28,c_107])).

tff(c_121,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_115])).

tff(c_26,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_39,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_partfun1(C_29,A_30)
      | ~ v1_funct_2(C_29,A_30,B_31)
      | ~ v1_funct_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | v1_xboole_0(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_39])).

tff(c_48,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_42])).

tff(c_52,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_18,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_61,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden('#skF_2'(A_36,B_37,C_38),A_36)
      | r2_relset_1(A_36,A_36,B_37,C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,A_36)))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_86,plain,(
    ! [B_41] :
      ( r2_hidden('#skF_2'('#skF_3',B_41,'#skF_5'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_3',B_41,'#skF_5')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_61])).

tff(c_92,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_86])).

tff(c_97,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_92])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_100])).

tff(c_106,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_45,plain,
    ( v1_partfun1('#skF_4','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_39])).

tff(c_51,plain,
    ( v1_partfun1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_45])).

tff(c_114,plain,(
    v1_partfun1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_51])).

tff(c_105,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_20,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_141,plain,(
    ! [D_51,C_52,A_53,B_54] :
      ( D_51 = C_52
      | ~ r1_partfun1(C_52,D_51)
      | ~ v1_partfun1(D_51,A_53)
      | ~ v1_partfun1(C_52,A_53)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_1(D_51)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_143,plain,(
    ! [A_53,B_54] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_53)
      | ~ v1_partfun1('#skF_4',A_53)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_141])).

tff(c_146,plain,(
    ! [A_53,B_54] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_53)
      | ~ v1_partfun1('#skF_4',A_53)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_143])).

tff(c_163,plain,(
    ! [A_56,B_57] :
      ( ~ v1_partfun1('#skF_5',A_56)
      | ~ v1_partfun1('#skF_4',A_56)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_166,plain,
    ( ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_partfun1('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_22,c_163])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_114,c_105,c_166])).

tff(c_171,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_178,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_18])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.34  
% 2.42/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.34  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k11_relat_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.42/1.34  
% 2.42/1.34  %Foreground sorts:
% 2.42/1.34  
% 2.42/1.34  
% 2.42/1.34  %Background operators:
% 2.42/1.34  
% 2.42/1.34  
% 2.42/1.34  %Foreground operators:
% 2.42/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.42/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.34  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.42/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.42/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.42/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.42/1.34  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.42/1.34  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.42/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.42/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.42/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.42/1.34  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.42/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.34  
% 2.42/1.35  tff(f_98, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_funct_2)).
% 2.42/1.35  tff(f_37, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.42/1.35  tff(f_63, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.42/1.35  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => ((![D]: (r2_hidden(D, A) => (k11_relat_1(B, D) = k11_relat_1(C, D)))) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relset_1)).
% 2.42/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.42/1.35  tff(f_80, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 2.42/1.35  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.35  tff(c_107, plain, (![A_42, B_43, C_44, D_45]: (r2_relset_1(A_42, B_43, C_44, C_44) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.42/1.35  tff(c_115, plain, (![C_46]: (r2_relset_1('#skF_3', '#skF_3', C_46, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_28, c_107])).
% 2.42/1.35  tff(c_121, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_115])).
% 2.42/1.35  tff(c_26, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.35  tff(c_24, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.35  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.35  tff(c_39, plain, (![C_29, A_30, B_31]: (v1_partfun1(C_29, A_30) | ~v1_funct_2(C_29, A_30, B_31) | ~v1_funct_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | v1_xboole_0(B_31))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.42/1.35  tff(c_42, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_39])).
% 2.42/1.35  tff(c_48, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_42])).
% 2.42/1.35  tff(c_52, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 2.42/1.35  tff(c_18, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.35  tff(c_61, plain, (![A_36, B_37, C_38]: (r2_hidden('#skF_2'(A_36, B_37, C_38), A_36) | r2_relset_1(A_36, A_36, B_37, C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))) | ~m1_subset_1(B_37, k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.42/1.35  tff(c_86, plain, (![B_41]: (r2_hidden('#skF_2'('#skF_3', B_41, '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', B_41, '#skF_5') | ~m1_subset_1(B_41, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_22, c_61])).
% 2.42/1.35  tff(c_92, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_28, c_86])).
% 2.42/1.35  tff(c_97, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_18, c_92])).
% 2.42/1.35  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.35  tff(c_100, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_97, c_2])).
% 2.42/1.35  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_100])).
% 2.42/1.35  tff(c_106, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 2.42/1.35  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.35  tff(c_30, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.35  tff(c_45, plain, (v1_partfun1('#skF_4', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_39])).
% 2.42/1.35  tff(c_51, plain, (v1_partfun1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_45])).
% 2.42/1.35  tff(c_114, plain, (v1_partfun1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_106, c_51])).
% 2.42/1.35  tff(c_105, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 2.42/1.35  tff(c_20, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.42/1.35  tff(c_141, plain, (![D_51, C_52, A_53, B_54]: (D_51=C_52 | ~r1_partfun1(C_52, D_51) | ~v1_partfun1(D_51, A_53) | ~v1_partfun1(C_52, A_53) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_1(D_51) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_1(C_52))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.42/1.35  tff(c_143, plain, (![A_53, B_54]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_53) | ~v1_partfun1('#skF_4', A_53) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_141])).
% 2.42/1.35  tff(c_146, plain, (![A_53, B_54]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_53) | ~v1_partfun1('#skF_4', A_53) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_143])).
% 2.42/1.35  tff(c_163, plain, (![A_56, B_57]: (~v1_partfun1('#skF_5', A_56) | ~v1_partfun1('#skF_4', A_56) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(splitLeft, [status(thm)], [c_146])).
% 2.42/1.35  tff(c_166, plain, (~v1_partfun1('#skF_5', '#skF_3') | ~v1_partfun1('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_22, c_163])).
% 2.42/1.35  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_114, c_105, c_166])).
% 2.42/1.35  tff(c_171, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_146])).
% 2.42/1.35  tff(c_178, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_18])).
% 2.42/1.35  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_178])).
% 2.42/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.35  
% 2.42/1.35  Inference rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Ref     : 0
% 2.42/1.35  #Sup     : 27
% 2.42/1.35  #Fact    : 0
% 2.42/1.35  #Define  : 0
% 2.42/1.35  #Split   : 4
% 2.42/1.35  #Chain   : 0
% 2.42/1.35  #Close   : 0
% 2.42/1.35  
% 2.42/1.35  Ordering : KBO
% 2.42/1.35  
% 2.42/1.35  Simplification rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Subsume      : 4
% 2.42/1.35  #Demod        : 32
% 2.42/1.35  #Tautology    : 11
% 2.42/1.35  #SimpNegUnit  : 3
% 2.42/1.35  #BackRed      : 10
% 2.42/1.35  
% 2.42/1.35  #Partial instantiations: 0
% 2.42/1.35  #Strategies tried      : 1
% 2.42/1.35  
% 2.42/1.35  Timing (in seconds)
% 2.42/1.36  ----------------------
% 2.42/1.36  Preprocessing        : 0.32
% 2.42/1.36  Parsing              : 0.18
% 2.42/1.36  CNF conversion       : 0.02
% 2.42/1.36  Main loop            : 0.21
% 2.42/1.36  Inferencing          : 0.08
% 2.42/1.36  Reduction            : 0.06
% 2.42/1.36  Demodulation         : 0.04
% 2.42/1.36  BG Simplification    : 0.01
% 2.42/1.36  Subsumption          : 0.03
% 2.42/1.36  Abstraction          : 0.01
% 2.42/1.36  MUC search           : 0.00
% 2.42/1.36  Cooper               : 0.00
% 2.42/1.36  Total                : 0.56
% 2.42/1.36  Index Insertion      : 0.00
% 2.42/1.36  Index Deletion       : 0.00
% 2.42/1.36  Index Matching       : 0.00
% 2.42/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
