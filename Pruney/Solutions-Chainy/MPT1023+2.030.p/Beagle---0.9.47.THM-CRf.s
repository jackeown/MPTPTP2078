%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:21 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 108 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  140 ( 401 expanded)
%              Number of equality atoms :    7 (  35 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_96,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_75,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_26,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_58,plain,(
    ! [B_29,A_30] :
      ( m1_subset_1(B_29,A_30)
      | ~ v1_xboole_0(B_29)
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    ! [E_22] :
      ( k1_funct_1('#skF_5',E_22) = k1_funct_1('#skF_4',E_22)
      | ~ m1_subset_1(E_22,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_68,plain,(
    ! [B_29] :
      ( k1_funct_1('#skF_5',B_29) = k1_funct_1('#skF_4',B_29)
      | ~ v1_xboole_0(B_29)
      | ~ v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_28])).

tff(c_100,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_131,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( r2_hidden('#skF_1'(A_49,B_50,C_51,D_52),A_49)
      | r2_relset_1(A_49,B_50,C_51,D_52)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_2(D_52,A_49,B_50)
      | ~ v1_funct_1(D_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_2(C_51,A_49,B_50)
      | ~ v1_funct_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_141,plain,(
    ! [C_51] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_51,'#skF_5'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_3',C_51,'#skF_5')
      | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2(C_51,'#skF_2','#skF_3')
      | ~ v1_funct_1(C_51) ) ),
    inference(resolution,[status(thm)],[c_30,c_131])).

tff(c_225,plain,(
    ! [C_65] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_65,'#skF_5'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_3',C_65,'#skF_5')
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2(C_65,'#skF_2','#skF_3')
      | ~ v1_funct_1(C_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_141])).

tff(c_236,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_225])).

tff(c_244,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_236])).

tff(c_245,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_244])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( m1_subset_1(B_4,A_3)
      | ~ r2_hidden(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_253,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_245,c_8])).

tff(c_257,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_253])).

tff(c_265,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_257,c_28])).

tff(c_22,plain,(
    ! [D_16,A_10,B_11,C_12] :
      ( k1_funct_1(D_16,'#skF_1'(A_10,B_11,C_12,D_16)) != k1_funct_1(C_12,'#skF_1'(A_10,B_11,C_12,D_16))
      | r2_relset_1(A_10,B_11,C_12,D_16)
      | ~ m1_subset_1(D_16,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_2(D_16,A_10,B_11)
      | ~ v1_funct_1(D_16)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_2(C_12,A_10,B_11)
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_269,plain,
    ( r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_22])).

tff(c_274,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_30,c_269])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_274])).

tff(c_278,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_311,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( r2_hidden('#skF_1'(A_78,B_79,C_80,D_81),A_78)
      | r2_relset_1(A_78,B_79,C_80,D_81)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_2(D_81,A_78,B_79)
      | ~ v1_funct_1(D_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_2(C_80,A_78,B_79)
      | ~ v1_funct_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_321,plain,(
    ! [C_80] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_80,'#skF_5'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_3',C_80,'#skF_5')
      | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2(C_80,'#skF_2','#skF_3')
      | ~ v1_funct_1(C_80) ) ),
    inference(resolution,[status(thm)],[c_30,c_311])).

tff(c_377,plain,(
    ! [C_94] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_94,'#skF_5'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_3',C_94,'#skF_5')
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2(C_94,'#skF_2','#skF_3')
      | ~ v1_funct_1(C_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_321])).

tff(c_388,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_377])).

tff(c_396,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2')
    | r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_388])).

tff(c_397,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_396])).

tff(c_18,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_296,plain,(
    ! [C_75,B_76,A_77] :
      ( ~ v1_xboole_0(C_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(C_75))
      | ~ r2_hidden(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_307,plain,(
    ! [B_6,A_77,A_5] :
      ( ~ v1_xboole_0(B_6)
      | ~ r2_hidden(A_77,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_18,c_296])).

tff(c_409,plain,(
    ! [B_95] :
      ( ~ v1_xboole_0(B_95)
      | ~ r1_tarski('#skF_2',B_95) ) ),
    inference(resolution,[status(thm)],[c_397,c_307])).

tff(c_413,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_409])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_413])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:37:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.40  
% 2.57/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.40  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.57/1.40  
% 2.57/1.40  %Foreground sorts:
% 2.57/1.40  
% 2.57/1.40  
% 2.57/1.40  %Background operators:
% 2.57/1.40  
% 2.57/1.40  
% 2.57/1.40  %Foreground operators:
% 2.57/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.57/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.40  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.57/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.57/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.57/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.57/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.57/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.57/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.40  
% 2.57/1.42  tff(f_96, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 2.57/1.42  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.57/1.42  tff(f_75, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 2.57/1.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.57/1.42  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.57/1.42  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.57/1.42  tff(c_26, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.57/1.42  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.57/1.42  tff(c_38, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.57/1.42  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.57/1.42  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.57/1.42  tff(c_32, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.57/1.42  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.57/1.42  tff(c_58, plain, (![B_29, A_30]: (m1_subset_1(B_29, A_30) | ~v1_xboole_0(B_29) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.57/1.42  tff(c_28, plain, (![E_22]: (k1_funct_1('#skF_5', E_22)=k1_funct_1('#skF_4', E_22) | ~m1_subset_1(E_22, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.57/1.42  tff(c_68, plain, (![B_29]: (k1_funct_1('#skF_5', B_29)=k1_funct_1('#skF_4', B_29) | ~v1_xboole_0(B_29) | ~v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_28])).
% 2.57/1.42  tff(c_100, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_68])).
% 2.57/1.42  tff(c_131, plain, (![A_49, B_50, C_51, D_52]: (r2_hidden('#skF_1'(A_49, B_50, C_51, D_52), A_49) | r2_relset_1(A_49, B_50, C_51, D_52) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_2(D_52, A_49, B_50) | ~v1_funct_1(D_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_2(C_51, A_49, B_50) | ~v1_funct_1(C_51))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.57/1.42  tff(c_141, plain, (![C_51]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_51, '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', C_51, '#skF_5') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(C_51, '#skF_2', '#skF_3') | ~v1_funct_1(C_51))), inference(resolution, [status(thm)], [c_30, c_131])).
% 2.57/1.42  tff(c_225, plain, (![C_65]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_65, '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', C_65, '#skF_5') | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(C_65, '#skF_2', '#skF_3') | ~v1_funct_1(C_65))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_141])).
% 2.57/1.42  tff(c_236, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_225])).
% 2.57/1.42  tff(c_244, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_236])).
% 2.57/1.42  tff(c_245, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_244])).
% 2.57/1.42  tff(c_8, plain, (![B_4, A_3]: (m1_subset_1(B_4, A_3) | ~r2_hidden(B_4, A_3) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.57/1.42  tff(c_253, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_245, c_8])).
% 2.57/1.42  tff(c_257, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_100, c_253])).
% 2.57/1.42  tff(c_265, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_257, c_28])).
% 2.57/1.42  tff(c_22, plain, (![D_16, A_10, B_11, C_12]: (k1_funct_1(D_16, '#skF_1'(A_10, B_11, C_12, D_16))!=k1_funct_1(C_12, '#skF_1'(A_10, B_11, C_12, D_16)) | r2_relset_1(A_10, B_11, C_12, D_16) | ~m1_subset_1(D_16, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~v1_funct_2(D_16, A_10, B_11) | ~v1_funct_1(D_16) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~v1_funct_2(C_12, A_10, B_11) | ~v1_funct_1(C_12))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.57/1.42  tff(c_269, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_265, c_22])).
% 2.57/1.42  tff(c_274, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_30, c_269])).
% 2.57/1.42  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_274])).
% 2.57/1.42  tff(c_278, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_68])).
% 2.57/1.42  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.42  tff(c_311, plain, (![A_78, B_79, C_80, D_81]: (r2_hidden('#skF_1'(A_78, B_79, C_80, D_81), A_78) | r2_relset_1(A_78, B_79, C_80, D_81) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_2(D_81, A_78, B_79) | ~v1_funct_1(D_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_2(C_80, A_78, B_79) | ~v1_funct_1(C_80))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.57/1.42  tff(c_321, plain, (![C_80]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_80, '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', C_80, '#skF_5') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(C_80, '#skF_2', '#skF_3') | ~v1_funct_1(C_80))), inference(resolution, [status(thm)], [c_30, c_311])).
% 2.57/1.42  tff(c_377, plain, (![C_94]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_94, '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', C_94, '#skF_5') | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(C_94, '#skF_2', '#skF_3') | ~v1_funct_1(C_94))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_321])).
% 2.57/1.42  tff(c_388, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_377])).
% 2.57/1.42  tff(c_396, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2') | r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_388])).
% 2.57/1.42  tff(c_397, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_396])).
% 2.57/1.42  tff(c_18, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.57/1.42  tff(c_296, plain, (![C_75, B_76, A_77]: (~v1_xboole_0(C_75) | ~m1_subset_1(B_76, k1_zfmisc_1(C_75)) | ~r2_hidden(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.57/1.42  tff(c_307, plain, (![B_6, A_77, A_5]: (~v1_xboole_0(B_6) | ~r2_hidden(A_77, A_5) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_18, c_296])).
% 2.57/1.42  tff(c_409, plain, (![B_95]: (~v1_xboole_0(B_95) | ~r1_tarski('#skF_2', B_95))), inference(resolution, [status(thm)], [c_397, c_307])).
% 2.57/1.42  tff(c_413, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_6, c_409])).
% 2.57/1.42  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_278, c_413])).
% 2.57/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.42  
% 2.57/1.42  Inference rules
% 2.57/1.42  ----------------------
% 2.57/1.42  #Ref     : 2
% 2.57/1.42  #Sup     : 73
% 2.57/1.42  #Fact    : 0
% 2.57/1.42  #Define  : 0
% 2.57/1.42  #Split   : 16
% 2.57/1.42  #Chain   : 0
% 2.57/1.42  #Close   : 0
% 2.57/1.42  
% 2.57/1.42  Ordering : KBO
% 2.57/1.42  
% 2.57/1.42  Simplification rules
% 2.57/1.42  ----------------------
% 2.57/1.42  #Subsume      : 14
% 2.57/1.42  #Demod        : 40
% 2.57/1.42  #Tautology    : 14
% 2.57/1.42  #SimpNegUnit  : 5
% 2.57/1.42  #BackRed      : 0
% 2.57/1.42  
% 2.57/1.42  #Partial instantiations: 0
% 2.57/1.42  #Strategies tried      : 1
% 2.57/1.42  
% 2.57/1.42  Timing (in seconds)
% 2.57/1.42  ----------------------
% 2.57/1.43  Preprocessing        : 0.30
% 2.57/1.43  Parsing              : 0.16
% 2.57/1.43  CNF conversion       : 0.02
% 2.57/1.43  Main loop            : 0.34
% 2.57/1.43  Inferencing          : 0.12
% 2.57/1.43  Reduction            : 0.11
% 2.57/1.43  Demodulation         : 0.08
% 2.57/1.43  BG Simplification    : 0.02
% 2.57/1.43  Subsumption          : 0.07
% 2.57/1.43  Abstraction          : 0.01
% 2.57/1.43  MUC search           : 0.00
% 2.57/1.43  Cooper               : 0.00
% 2.57/1.43  Total                : 0.68
% 2.57/1.43  Index Insertion      : 0.00
% 2.57/1.43  Index Deletion       : 0.00
% 2.57/1.43  Index Matching       : 0.00
% 2.57/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
