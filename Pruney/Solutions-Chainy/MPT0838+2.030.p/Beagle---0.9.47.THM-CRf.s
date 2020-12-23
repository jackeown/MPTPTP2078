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
% DateTime   : Thu Dec  3 10:08:13 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 145 expanded)
%              Number of leaves         :   27 (  59 expanded)
%              Depth                    :    7
%              Number of atoms          :   81 ( 297 expanded)
%              Number of equality atoms :   36 ( 111 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_48,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_48])).

tff(c_10,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_60,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_10])).

tff(c_62,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    ! [A_42,B_43,C_44] :
      ( k2_relset_1(A_42,B_43,C_44) = k2_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_72,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_68])).

tff(c_22,plain,(
    ! [D_30] :
      ( ~ r2_hidden(D_30,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_30,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_78,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k2_relat_1('#skF_4'))
      | ~ m1_subset_1(D_45,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_22])).

tff(c_82,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_78])).

tff(c_85,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_82])).

tff(c_98,plain,(
    ! [A_49,B_50,C_51] :
      ( m1_subset_1(k2_relset_1(A_49,B_50,C_51),k1_zfmisc_1(B_50))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_115,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_98])).

tff(c_121,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_115])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,(
    ! [A_52] :
      ( m1_subset_1(A_52,'#skF_3')
      | ~ r2_hidden(A_52,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_121,c_4])).

tff(c_129,plain,
    ( m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_125])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_85,c_129])).

tff(c_134,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_8,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_142,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_134,c_8])).

tff(c_12,plain,(
    ! [A_6] :
      ( k1_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_59,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_12])).

tff(c_61,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_136,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_61])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_136])).

tff(c_159,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_24,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_164,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_24])).

tff(c_160,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_175,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_160])).

tff(c_228,plain,(
    ! [A_64,B_65,C_66] :
      ( k1_relset_1(A_64,B_65,C_66) = k1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_231,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_228])).

tff(c_233,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_231])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:33:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.24  
% 2.14/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.24  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.14/1.24  
% 2.14/1.24  %Foreground sorts:
% 2.14/1.24  
% 2.14/1.24  
% 2.14/1.24  %Background operators:
% 2.14/1.24  
% 2.14/1.24  
% 2.14/1.24  %Foreground operators:
% 2.14/1.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.14/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.14/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.14/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.24  
% 2.14/1.25  tff(f_87, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 2.14/1.25  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.14/1.25  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.14/1.25  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.14/1.25  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.14/1.25  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.14/1.25  tff(f_39, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.14/1.25  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.14/1.25  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.14/1.25  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.14/1.25  tff(c_48, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.14/1.25  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_48])).
% 2.14/1.25  tff(c_10, plain, (![A_6]: (k2_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.14/1.25  tff(c_60, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_52, c_10])).
% 2.14/1.25  tff(c_62, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 2.14/1.25  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.25  tff(c_68, plain, (![A_42, B_43, C_44]: (k2_relset_1(A_42, B_43, C_44)=k2_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.14/1.25  tff(c_72, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_68])).
% 2.14/1.25  tff(c_22, plain, (![D_30]: (~r2_hidden(D_30, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_30, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.14/1.25  tff(c_78, plain, (![D_45]: (~r2_hidden(D_45, k2_relat_1('#skF_4')) | ~m1_subset_1(D_45, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_22])).
% 2.14/1.25  tff(c_82, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_78])).
% 2.14/1.25  tff(c_85, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_82])).
% 2.14/1.25  tff(c_98, plain, (![A_49, B_50, C_51]: (m1_subset_1(k2_relset_1(A_49, B_50, C_51), k1_zfmisc_1(B_50)) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.14/1.25  tff(c_115, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_98])).
% 2.14/1.25  tff(c_121, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_115])).
% 2.14/1.25  tff(c_4, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.25  tff(c_125, plain, (![A_52]: (m1_subset_1(A_52, '#skF_3') | ~r2_hidden(A_52, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_121, c_4])).
% 2.14/1.25  tff(c_129, plain, (m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_125])).
% 2.14/1.25  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_85, c_129])).
% 2.14/1.25  tff(c_134, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 2.14/1.25  tff(c_8, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.14/1.25  tff(c_142, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_134, c_8])).
% 2.14/1.25  tff(c_12, plain, (![A_6]: (k1_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.14/1.25  tff(c_59, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_52, c_12])).
% 2.14/1.25  tff(c_61, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_59])).
% 2.14/1.25  tff(c_136, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_61])).
% 2.14/1.25  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_136])).
% 2.14/1.25  tff(c_159, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_59])).
% 2.14/1.25  tff(c_24, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.14/1.25  tff(c_164, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_24])).
% 2.14/1.25  tff(c_160, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_59])).
% 2.14/1.25  tff(c_175, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_160])).
% 2.14/1.25  tff(c_228, plain, (![A_64, B_65, C_66]: (k1_relset_1(A_64, B_65, C_66)=k1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.14/1.25  tff(c_231, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_228])).
% 2.14/1.25  tff(c_233, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_175, c_231])).
% 2.14/1.25  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_233])).
% 2.14/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.25  
% 2.14/1.25  Inference rules
% 2.14/1.25  ----------------------
% 2.14/1.25  #Ref     : 0
% 2.14/1.25  #Sup     : 44
% 2.14/1.25  #Fact    : 0
% 2.14/1.25  #Define  : 0
% 2.14/1.25  #Split   : 2
% 2.14/1.25  #Chain   : 0
% 2.14/1.25  #Close   : 0
% 2.14/1.25  
% 2.14/1.25  Ordering : KBO
% 2.14/1.25  
% 2.14/1.25  Simplification rules
% 2.14/1.25  ----------------------
% 2.14/1.25  #Subsume      : 2
% 2.14/1.25  #Demod        : 39
% 2.14/1.25  #Tautology    : 28
% 2.14/1.25  #SimpNegUnit  : 4
% 2.14/1.25  #BackRed      : 16
% 2.14/1.25  
% 2.14/1.25  #Partial instantiations: 0
% 2.14/1.25  #Strategies tried      : 1
% 2.14/1.25  
% 2.14/1.25  Timing (in seconds)
% 2.14/1.25  ----------------------
% 2.14/1.26  Preprocessing        : 0.30
% 2.14/1.26  Parsing              : 0.16
% 2.14/1.26  CNF conversion       : 0.02
% 2.14/1.26  Main loop            : 0.18
% 2.14/1.26  Inferencing          : 0.07
% 2.14/1.26  Reduction            : 0.06
% 2.14/1.26  Demodulation         : 0.04
% 2.14/1.26  BG Simplification    : 0.01
% 2.14/1.26  Subsumption          : 0.03
% 2.14/1.26  Abstraction          : 0.01
% 2.14/1.26  MUC search           : 0.00
% 2.14/1.26  Cooper               : 0.00
% 2.14/1.26  Total                : 0.51
% 2.14/1.26  Index Insertion      : 0.00
% 2.14/1.26  Index Deletion       : 0.00
% 2.14/1.26  Index Matching       : 0.00
% 2.14/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
