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
% DateTime   : Thu Dec  3 10:16:20 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 202 expanded)
%              Number of leaves         :   23 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  134 ( 716 expanded)
%              Number of equality atoms :   14 (  70 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ! [E] :
                ( r2_hidden(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) )
           => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_80,plain,(
    ! [A_40,B_41,D_42] :
      ( r2_relset_1(A_40,B_41,D_42,D_42)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_89,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_80])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_105,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( r2_hidden('#skF_1'(A_50,B_51,C_52,D_53),A_50)
      | r2_relset_1(A_50,B_51,C_52,D_53)
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ v1_funct_2(D_53,A_50,B_51)
      | ~ v1_funct_1(D_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ v1_funct_2(C_52,A_50,B_51)
      | ~ v1_funct_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_110,plain,(
    ! [C_52] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_52,'#skF_4'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_3',C_52,'#skF_4')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2(C_52,'#skF_2','#skF_3')
      | ~ v1_funct_1(C_52) ) ),
    inference(resolution,[status(thm)],[c_32,c_105])).

tff(c_120,plain,(
    ! [C_54] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_54,'#skF_4'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_3',C_54,'#skF_4')
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2(C_54,'#skF_2','#skF_3')
      | ~ v1_funct_1(C_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_110])).

tff(c_130,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_2')
    | r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_120])).

tff(c_137,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_2')
    | r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_130])).

tff(c_138,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_16,plain,(
    ! [D_12,C_11,A_9,B_10] :
      ( D_12 = C_11
      | ~ r2_relset_1(A_9,B_10,C_11,D_12)
      | ~ m1_subset_1(D_12,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_159,plain,
    ( '#skF_5' = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_138,c_16])).

tff(c_162,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_32,c_159])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_168,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_22])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_168])).

tff(c_178,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_65,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_xboole_0(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_77,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_65])).

tff(c_79,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_177,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( m1_subset_1(B_4,A_3)
      | ~ r2_hidden(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_181,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_177,c_4])).

tff(c_184,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_181])).

tff(c_24,plain,(
    ! [E_25] :
      ( k1_funct_1('#skF_5',E_25) = k1_funct_1('#skF_4',E_25)
      | ~ m1_subset_1(E_25,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_191,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_184,c_24])).

tff(c_18,plain,(
    ! [D_19,A_13,B_14,C_15] :
      ( k1_funct_1(D_19,'#skF_1'(A_13,B_14,C_15,D_19)) != k1_funct_1(C_15,'#skF_1'(A_13,B_14,C_15,D_19))
      | r2_relset_1(A_13,B_14,C_15,D_19)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_2(D_19,A_13,B_14)
      | ~ v1_funct_1(D_19)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_2(C_15,A_13,B_14)
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_199,plain,
    ( r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_18])).

tff(c_204,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_36,c_34,c_32,c_199])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_204])).

tff(c_207,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_208,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_220,plain,(
    ! [A_60] :
      ( A_60 = '#skF_2'
      | ~ v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_208,c_2])).

tff(c_233,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_207,c_220])).

tff(c_78,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_65])).

tff(c_216,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_78])).

tff(c_230,plain,(
    '#skF_5' = '#skF_2' ),
    inference(resolution,[status(thm)],[c_216,c_220])).

tff(c_237,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_22])).

tff(c_274,plain,(
    ~ r2_relset_1('#skF_4','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_233,c_237])).

tff(c_249,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_32])).

tff(c_14,plain,(
    ! [A_9,B_10,D_12] :
      ( r2_relset_1(A_9,B_10,D_12,D_12)
      | ~ m1_subset_1(D_12,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_276,plain,(
    r2_relset_1('#skF_4','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_249,c_14])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.75  
% 2.75/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.75  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.75/1.75  
% 2.75/1.75  %Foreground sorts:
% 2.75/1.75  
% 2.75/1.75  
% 2.75/1.75  %Background operators:
% 2.75/1.75  
% 2.75/1.75  
% 2.75/1.75  %Foreground operators:
% 2.75/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.75/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.75  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.75/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.75  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.75/1.75  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.75  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.75/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.75/1.75  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.75/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.75  
% 2.75/1.78  tff(f_102, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 2.75/1.78  tff(f_61, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.75/1.78  tff(f_81, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 2.75/1.78  tff(f_53, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 2.75/1.78  tff(f_46, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.75/1.78  tff(f_33, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.75/1.78  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.75/1.78  tff(c_80, plain, (![A_40, B_41, D_42]: (r2_relset_1(A_40, B_41, D_42, D_42) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.75/1.78  tff(c_89, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_80])).
% 2.75/1.78  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.75/1.78  tff(c_30, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.75/1.78  tff(c_28, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.75/1.78  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.75/1.78  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.75/1.78  tff(c_105, plain, (![A_50, B_51, C_52, D_53]: (r2_hidden('#skF_1'(A_50, B_51, C_52, D_53), A_50) | r2_relset_1(A_50, B_51, C_52, D_53) | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~v1_funct_2(D_53, A_50, B_51) | ~v1_funct_1(D_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~v1_funct_2(C_52, A_50, B_51) | ~v1_funct_1(C_52))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.75/1.78  tff(c_110, plain, (![C_52]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_52, '#skF_4'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', C_52, '#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(C_52, '#skF_2', '#skF_3') | ~v1_funct_1(C_52))), inference(resolution, [status(thm)], [c_32, c_105])).
% 2.75/1.78  tff(c_120, plain, (![C_54]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_54, '#skF_4'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', C_54, '#skF_4') | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(C_54, '#skF_2', '#skF_3') | ~v1_funct_1(C_54))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_110])).
% 2.75/1.78  tff(c_130, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_120])).
% 2.75/1.78  tff(c_137, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_130])).
% 2.75/1.78  tff(c_138, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_137])).
% 2.75/1.78  tff(c_16, plain, (![D_12, C_11, A_9, B_10]: (D_12=C_11 | ~r2_relset_1(A_9, B_10, C_11, D_12) | ~m1_subset_1(D_12, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.75/1.78  tff(c_159, plain, ('#skF_5'='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_138, c_16])).
% 2.75/1.78  tff(c_162, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_32, c_159])).
% 2.75/1.78  tff(c_22, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.75/1.78  tff(c_168, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_22])).
% 2.75/1.78  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_168])).
% 2.75/1.78  tff(c_178, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_137])).
% 2.75/1.78  tff(c_65, plain, (![C_37, A_38, B_39]: (v1_xboole_0(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.75/1.78  tff(c_77, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_65])).
% 2.75/1.78  tff(c_79, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_77])).
% 2.75/1.78  tff(c_177, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_137])).
% 2.75/1.78  tff(c_4, plain, (![B_4, A_3]: (m1_subset_1(B_4, A_3) | ~r2_hidden(B_4, A_3) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.75/1.78  tff(c_181, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_177, c_4])).
% 2.75/1.78  tff(c_184, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_79, c_181])).
% 2.75/1.78  tff(c_24, plain, (![E_25]: (k1_funct_1('#skF_5', E_25)=k1_funct_1('#skF_4', E_25) | ~m1_subset_1(E_25, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.75/1.78  tff(c_191, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_184, c_24])).
% 2.75/1.78  tff(c_18, plain, (![D_19, A_13, B_14, C_15]: (k1_funct_1(D_19, '#skF_1'(A_13, B_14, C_15, D_19))!=k1_funct_1(C_15, '#skF_1'(A_13, B_14, C_15, D_19)) | r2_relset_1(A_13, B_14, C_15, D_19) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(D_19, A_13, B_14) | ~v1_funct_1(D_19) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(C_15, A_13, B_14) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.75/1.78  tff(c_199, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_191, c_18])).
% 2.75/1.78  tff(c_204, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_36, c_34, c_32, c_199])).
% 2.75/1.78  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_204])).
% 2.75/1.78  tff(c_207, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_77])).
% 2.75/1.78  tff(c_208, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_77])).
% 2.75/1.78  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.78  tff(c_220, plain, (![A_60]: (A_60='#skF_2' | ~v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_208, c_2])).
% 2.75/1.78  tff(c_233, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_207, c_220])).
% 2.75/1.78  tff(c_78, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_65])).
% 2.75/1.78  tff(c_216, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_78])).
% 2.75/1.78  tff(c_230, plain, ('#skF_5'='#skF_2'), inference(resolution, [status(thm)], [c_216, c_220])).
% 2.75/1.78  tff(c_237, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_22])).
% 2.75/1.78  tff(c_274, plain, (~r2_relset_1('#skF_4', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_233, c_233, c_237])).
% 2.75/1.78  tff(c_249, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_32])).
% 2.75/1.78  tff(c_14, plain, (![A_9, B_10, D_12]: (r2_relset_1(A_9, B_10, D_12, D_12) | ~m1_subset_1(D_12, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.75/1.78  tff(c_276, plain, (r2_relset_1('#skF_4', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_249, c_14])).
% 2.75/1.78  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_274, c_276])).
% 2.75/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.78  
% 2.75/1.78  Inference rules
% 2.75/1.78  ----------------------
% 2.75/1.78  #Ref     : 1
% 2.75/1.78  #Sup     : 46
% 2.75/1.78  #Fact    : 0
% 2.75/1.78  #Define  : 0
% 2.75/1.78  #Split   : 3
% 2.75/1.78  #Chain   : 0
% 2.75/1.78  #Close   : 0
% 2.75/1.78  
% 2.75/1.78  Ordering : KBO
% 2.75/1.78  
% 2.75/1.78  Simplification rules
% 2.75/1.78  ----------------------
% 2.75/1.78  #Subsume      : 10
% 2.75/1.78  #Demod        : 61
% 2.75/1.78  #Tautology    : 24
% 2.75/1.78  #SimpNegUnit  : 4
% 2.75/1.78  #BackRed      : 19
% 2.75/1.78  
% 2.75/1.78  #Partial instantiations: 0
% 2.75/1.78  #Strategies tried      : 1
% 2.75/1.78  
% 2.75/1.78  Timing (in seconds)
% 2.75/1.78  ----------------------
% 2.98/1.78  Preprocessing        : 0.50
% 2.98/1.78  Parsing              : 0.26
% 2.98/1.78  CNF conversion       : 0.04
% 2.98/1.78  Main loop            : 0.35
% 2.98/1.78  Inferencing          : 0.12
% 2.98/1.78  Reduction            : 0.11
% 2.98/1.78  Demodulation         : 0.08
% 2.98/1.78  BG Simplification    : 0.02
% 3.00/1.78  Subsumption          : 0.07
% 3.00/1.78  Abstraction          : 0.02
% 3.00/1.78  MUC search           : 0.00
% 3.00/1.78  Cooper               : 0.00
% 3.00/1.78  Total                : 0.91
% 3.00/1.78  Index Insertion      : 0.00
% 3.00/1.78  Index Deletion       : 0.00
% 3.00/1.78  Index Matching       : 0.00
% 3.00/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
