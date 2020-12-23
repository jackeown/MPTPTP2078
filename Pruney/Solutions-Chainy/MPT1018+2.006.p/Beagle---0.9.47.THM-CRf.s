%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:46 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 157 expanded)
%              Number of leaves         :   26 (  70 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 502 expanded)
%              Number of equality atoms :   35 ( 198 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_84,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
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

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_28,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_47,plain,(
    ! [C_19,A_20,B_21] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_51,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_47])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_55,plain,(
    ! [A_25,B_26,C_27] :
      ( k1_relset_1(A_25,B_26,C_27) = k1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_59,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_55])).

tff(c_77,plain,(
    ! [B_36,A_37,C_38] :
      ( k1_xboole_0 = B_36
      | k1_relset_1(A_37,B_36,C_38) = A_37
      | ~ v1_funct_2(C_38,A_37,B_36)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_37,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_80,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_77])).

tff(c_83,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_59,c_80])).

tff(c_84,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_34,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_115,plain,(
    ! [C_42,B_43,A_44] :
      ( C_42 = B_43
      | k1_funct_1(A_44,C_42) != k1_funct_1(A_44,B_43)
      | ~ r2_hidden(C_42,k1_relat_1(A_44))
      | ~ r2_hidden(B_43,k1_relat_1(A_44))
      | ~ v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_121,plain,(
    ! [B_43] :
      ( B_43 = '#skF_5'
      | k1_funct_1('#skF_4',B_43) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_43,k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_115])).

tff(c_128,plain,(
    ! [B_45] :
      ( B_45 = '#skF_5'
      | k1_funct_1('#skF_4',B_45) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(B_45,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_42,c_36,c_84,c_34,c_84,c_121])).

tff(c_131,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_32,c_128])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_131])).

tff(c_140,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_139,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_24,plain,(
    ! [B_15,C_16] :
      ( k1_relset_1(k1_xboole_0,B_15,C_16) = k1_xboole_0
      | ~ v1_funct_2(C_16,k1_xboole_0,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_166,plain,(
    ! [B_52,C_53] :
      ( k1_relset_1('#skF_3',B_52,C_53) = '#skF_3'
      | ~ v1_funct_2(C_53,'#skF_3',B_52)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_52))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_139,c_139,c_139,c_24])).

tff(c_169,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_166])).

tff(c_172,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_59,c_169])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:24:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.23  
% 2.10/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.23  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.10/1.23  
% 2.10/1.23  %Foreground sorts:
% 2.10/1.23  
% 2.10/1.23  
% 2.10/1.23  %Background operators:
% 2.10/1.23  
% 2.10/1.23  
% 2.10/1.23  %Foreground operators:
% 2.10/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.10/1.23  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.10/1.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.10/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.10/1.23  tff('#skF_6', type, '#skF_6': $i).
% 2.10/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.10/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.10/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.23  
% 2.12/1.24  tff(f_84, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 2.12/1.24  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.12/1.24  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.12/1.24  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.12/1.24  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 2.12/1.24  tff(c_28, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.24  tff(c_32, plain, (r2_hidden('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.24  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.24  tff(c_47, plain, (![C_19, A_20, B_21]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.24  tff(c_51, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_47])).
% 2.12/1.24  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.24  tff(c_36, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.24  tff(c_40, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.24  tff(c_55, plain, (![A_25, B_26, C_27]: (k1_relset_1(A_25, B_26, C_27)=k1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.12/1.24  tff(c_59, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_55])).
% 2.12/1.24  tff(c_77, plain, (![B_36, A_37, C_38]: (k1_xboole_0=B_36 | k1_relset_1(A_37, B_36, C_38)=A_37 | ~v1_funct_2(C_38, A_37, B_36) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_37, B_36))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.24  tff(c_80, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_77])).
% 2.12/1.24  tff(c_83, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_59, c_80])).
% 2.12/1.24  tff(c_84, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_83])).
% 2.12/1.24  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.24  tff(c_30, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.24  tff(c_115, plain, (![C_42, B_43, A_44]: (C_42=B_43 | k1_funct_1(A_44, C_42)!=k1_funct_1(A_44, B_43) | ~r2_hidden(C_42, k1_relat_1(A_44)) | ~r2_hidden(B_43, k1_relat_1(A_44)) | ~v2_funct_1(A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.12/1.24  tff(c_121, plain, (![B_43]: (B_43='#skF_5' | k1_funct_1('#skF_4', B_43)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_43, k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_115])).
% 2.12/1.24  tff(c_128, plain, (![B_45]: (B_45='#skF_5' | k1_funct_1('#skF_4', B_45)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(B_45, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_42, c_36, c_84, c_34, c_84, c_121])).
% 2.12/1.24  tff(c_131, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_32, c_128])).
% 2.12/1.24  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_131])).
% 2.12/1.24  tff(c_140, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(splitRight, [status(thm)], [c_83])).
% 2.12/1.24  tff(c_139, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_83])).
% 2.12/1.24  tff(c_24, plain, (![B_15, C_16]: (k1_relset_1(k1_xboole_0, B_15, C_16)=k1_xboole_0 | ~v1_funct_2(C_16, k1_xboole_0, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_15))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.24  tff(c_166, plain, (![B_52, C_53]: (k1_relset_1('#skF_3', B_52, C_53)='#skF_3' | ~v1_funct_2(C_53, '#skF_3', B_52) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_52))))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_139, c_139, c_139, c_24])).
% 2.12/1.24  tff(c_169, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_166])).
% 2.12/1.24  tff(c_172, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_59, c_169])).
% 2.12/1.24  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_172])).
% 2.12/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.24  
% 2.12/1.24  Inference rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Ref     : 1
% 2.12/1.24  #Sup     : 27
% 2.12/1.24  #Fact    : 0
% 2.12/1.24  #Define  : 0
% 2.12/1.24  #Split   : 1
% 2.12/1.24  #Chain   : 0
% 2.12/1.24  #Close   : 0
% 2.12/1.24  
% 2.12/1.24  Ordering : KBO
% 2.12/1.24  
% 2.12/1.24  Simplification rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Subsume      : 1
% 2.12/1.24  #Demod        : 47
% 2.12/1.24  #Tautology    : 19
% 2.12/1.24  #SimpNegUnit  : 2
% 2.12/1.24  #BackRed      : 6
% 2.12/1.24  
% 2.12/1.24  #Partial instantiations: 0
% 2.12/1.24  #Strategies tried      : 1
% 2.12/1.24  
% 2.12/1.24  Timing (in seconds)
% 2.12/1.24  ----------------------
% 2.12/1.24  Preprocessing        : 0.31
% 2.12/1.24  Parsing              : 0.16
% 2.12/1.24  CNF conversion       : 0.02
% 2.12/1.25  Main loop            : 0.18
% 2.12/1.25  Inferencing          : 0.06
% 2.12/1.25  Reduction            : 0.05
% 2.12/1.25  Demodulation         : 0.04
% 2.12/1.25  BG Simplification    : 0.01
% 2.12/1.25  Subsumption          : 0.03
% 2.12/1.25  Abstraction          : 0.01
% 2.12/1.25  MUC search           : 0.00
% 2.12/1.25  Cooper               : 0.00
% 2.12/1.25  Total                : 0.51
% 2.12/1.25  Index Insertion      : 0.00
% 2.12/1.25  Index Deletion       : 0.00
% 2.12/1.25  Index Matching       : 0.00
% 2.12/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
