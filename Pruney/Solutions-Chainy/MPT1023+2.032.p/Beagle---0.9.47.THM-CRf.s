%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:21 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 112 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  144 ( 408 expanded)
%              Number of equality atoms :    6 (  34 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_84,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_30,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_38,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_73,plain,(
    ! [B_37,A_38] :
      ( m1_subset_1(B_37,A_38)
      | ~ v1_xboole_0(B_37)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    ! [E_29] :
      ( k1_funct_1('#skF_5',E_29) = k1_funct_1('#skF_6',E_29)
      | ~ m1_subset_1(E_29,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_86,plain,(
    ! [B_37] :
      ( k1_funct_1('#skF_5',B_37) = k1_funct_1('#skF_6',B_37)
      | ~ v1_xboole_0(B_37)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_73,c_32])).

tff(c_91,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_323,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( r2_hidden('#skF_2'(A_100,B_101,C_102,D_103),A_100)
      | r2_relset_1(A_100,B_101,C_102,D_103)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_2(D_103,A_100,B_101)
      | ~ v1_funct_1(D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_2(C_102,A_100,B_101)
      | ~ v1_funct_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_334,plain,(
    ! [C_102] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4',C_102,'#skF_6'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_4',C_102,'#skF_6')
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2(C_102,'#skF_3','#skF_4')
      | ~ v1_funct_1(C_102) ) ),
    inference(resolution,[status(thm)],[c_34,c_323])).

tff(c_550,plain,(
    ! [C_131] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4',C_131,'#skF_6'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_4',C_131,'#skF_6')
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2(C_131,'#skF_3','#skF_4')
      | ~ v1_funct_1(C_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_334])).

tff(c_572,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_550])).

tff(c_586,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_572])).

tff(c_587,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_586])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( m1_subset_1(B_7,A_6)
      | ~ r2_hidden(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_594,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_587,c_8])).

tff(c_599,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_594])).

tff(c_628,plain,(
    k1_funct_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_599,c_32])).

tff(c_26,plain,(
    ! [D_23,A_17,B_18,C_19] :
      ( k1_funct_1(D_23,'#skF_2'(A_17,B_18,C_19,D_23)) != k1_funct_1(C_19,'#skF_2'(A_17,B_18,C_19,D_23))
      | r2_relset_1(A_17,B_18,C_19,D_23)
      | ~ m1_subset_1(D_23,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_2(D_23,A_17,B_18)
      | ~ v1_funct_1(D_23)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_2(C_19,A_17,B_18)
      | ~ v1_funct_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_735,plain,
    ( r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_26])).

tff(c_740,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_34,c_735])).

tff(c_742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_740])).

tff(c_744,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_745,plain,(
    ! [A_137,B_138] :
      ( ~ r2_hidden('#skF_1'(A_137,B_138),B_138)
      | r1_tarski(A_137,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_755,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_745])).

tff(c_962,plain,(
    ! [A_187,B_188,C_189,D_190] :
      ( r2_hidden('#skF_2'(A_187,B_188,C_189,D_190),A_187)
      | r2_relset_1(A_187,B_188,C_189,D_190)
      | ~ m1_subset_1(D_190,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_2(D_190,A_187,B_188)
      | ~ v1_funct_1(D_190)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_2(C_189,A_187,B_188)
      | ~ v1_funct_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_973,plain,(
    ! [C_189] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4',C_189,'#skF_6'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_4',C_189,'#skF_6')
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2(C_189,'#skF_3','#skF_4')
      | ~ v1_funct_1(C_189) ) ),
    inference(resolution,[status(thm)],[c_34,c_962])).

tff(c_1014,plain,(
    ! [C_198] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4',C_198,'#skF_6'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_4',C_198,'#skF_6')
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2(C_198,'#skF_3','#skF_4')
      | ~ v1_funct_1(C_198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_973])).

tff(c_1032,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1014])).

tff(c_1043,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1032])).

tff(c_1044,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1043])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_767,plain,(
    ! [C_144,B_145,A_146] :
      ( ~ v1_xboole_0(C_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(C_144))
      | ~ r2_hidden(A_146,B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_778,plain,(
    ! [B_9,A_146,A_8] :
      ( ~ v1_xboole_0(B_9)
      | ~ r2_hidden(A_146,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_767])).

tff(c_1056,plain,(
    ! [B_199] :
      ( ~ v1_xboole_0(B_199)
      | ~ r1_tarski('#skF_3',B_199) ) ),
    inference(resolution,[status(thm)],[c_1044,c_778])).

tff(c_1064,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_755,c_1056])).

tff(c_1071,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_744,c_1064])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.59  
% 3.23/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.59  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 3.23/1.59  
% 3.23/1.59  %Foreground sorts:
% 3.23/1.59  
% 3.23/1.59  
% 3.23/1.59  %Background operators:
% 3.23/1.59  
% 3.23/1.59  
% 3.23/1.59  %Foreground operators:
% 3.23/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.23/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.59  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.23/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.23/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.23/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.23/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.23/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.23/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.23/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.59  
% 3.23/1.61  tff(f_105, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 3.23/1.61  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.23/1.61  tff(f_84, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 3.23/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.23/1.61  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.23/1.61  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.23/1.61  tff(c_30, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.61  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.61  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.61  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.61  tff(c_38, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.61  tff(c_36, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.61  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.61  tff(c_73, plain, (![B_37, A_38]: (m1_subset_1(B_37, A_38) | ~v1_xboole_0(B_37) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.23/1.61  tff(c_32, plain, (![E_29]: (k1_funct_1('#skF_5', E_29)=k1_funct_1('#skF_6', E_29) | ~m1_subset_1(E_29, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.61  tff(c_86, plain, (![B_37]: (k1_funct_1('#skF_5', B_37)=k1_funct_1('#skF_6', B_37) | ~v1_xboole_0(B_37) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_73, c_32])).
% 3.23/1.61  tff(c_91, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_86])).
% 3.23/1.61  tff(c_323, plain, (![A_100, B_101, C_102, D_103]: (r2_hidden('#skF_2'(A_100, B_101, C_102, D_103), A_100) | r2_relset_1(A_100, B_101, C_102, D_103) | ~m1_subset_1(D_103, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~v1_funct_2(D_103, A_100, B_101) | ~v1_funct_1(D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~v1_funct_2(C_102, A_100, B_101) | ~v1_funct_1(C_102))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.23/1.61  tff(c_334, plain, (![C_102]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', C_102, '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', C_102, '#skF_6') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2(C_102, '#skF_3', '#skF_4') | ~v1_funct_1(C_102))), inference(resolution, [status(thm)], [c_34, c_323])).
% 3.23/1.61  tff(c_550, plain, (![C_131]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', C_131, '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', C_131, '#skF_6') | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2(C_131, '#skF_3', '#skF_4') | ~v1_funct_1(C_131))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_334])).
% 3.23/1.61  tff(c_572, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_550])).
% 3.23/1.61  tff(c_586, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_572])).
% 3.23/1.61  tff(c_587, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_586])).
% 3.23/1.61  tff(c_8, plain, (![B_7, A_6]: (m1_subset_1(B_7, A_6) | ~r2_hidden(B_7, A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.23/1.61  tff(c_594, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_587, c_8])).
% 3.23/1.61  tff(c_599, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_91, c_594])).
% 3.23/1.61  tff(c_628, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_599, c_32])).
% 3.23/1.61  tff(c_26, plain, (![D_23, A_17, B_18, C_19]: (k1_funct_1(D_23, '#skF_2'(A_17, B_18, C_19, D_23))!=k1_funct_1(C_19, '#skF_2'(A_17, B_18, C_19, D_23)) | r2_relset_1(A_17, B_18, C_19, D_23) | ~m1_subset_1(D_23, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_2(D_23, A_17, B_18) | ~v1_funct_1(D_23) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_2(C_19, A_17, B_18) | ~v1_funct_1(C_19))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.23/1.61  tff(c_735, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_628, c_26])).
% 3.23/1.61  tff(c_740, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_34, c_735])).
% 3.23/1.61  tff(c_742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_740])).
% 3.23/1.61  tff(c_744, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_86])).
% 3.23/1.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.23/1.61  tff(c_745, plain, (![A_137, B_138]: (~r2_hidden('#skF_1'(A_137, B_138), B_138) | r1_tarski(A_137, B_138))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.23/1.61  tff(c_755, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_745])).
% 3.23/1.61  tff(c_962, plain, (![A_187, B_188, C_189, D_190]: (r2_hidden('#skF_2'(A_187, B_188, C_189, D_190), A_187) | r2_relset_1(A_187, B_188, C_189, D_190) | ~m1_subset_1(D_190, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_2(D_190, A_187, B_188) | ~v1_funct_1(D_190) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_2(C_189, A_187, B_188) | ~v1_funct_1(C_189))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.23/1.61  tff(c_973, plain, (![C_189]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', C_189, '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', C_189, '#skF_6') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2(C_189, '#skF_3', '#skF_4') | ~v1_funct_1(C_189))), inference(resolution, [status(thm)], [c_34, c_962])).
% 3.23/1.61  tff(c_1014, plain, (![C_198]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', C_198, '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', C_198, '#skF_6') | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2(C_198, '#skF_3', '#skF_4') | ~v1_funct_1(C_198))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_973])).
% 3.23/1.61  tff(c_1032, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_1014])).
% 3.23/1.61  tff(c_1043, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3') | r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1032])).
% 3.23/1.61  tff(c_1044, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_1043])).
% 3.23/1.61  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.23/1.61  tff(c_767, plain, (![C_144, B_145, A_146]: (~v1_xboole_0(C_144) | ~m1_subset_1(B_145, k1_zfmisc_1(C_144)) | ~r2_hidden(A_146, B_145))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.23/1.61  tff(c_778, plain, (![B_9, A_146, A_8]: (~v1_xboole_0(B_9) | ~r2_hidden(A_146, A_8) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_18, c_767])).
% 3.23/1.61  tff(c_1056, plain, (![B_199]: (~v1_xboole_0(B_199) | ~r1_tarski('#skF_3', B_199))), inference(resolution, [status(thm)], [c_1044, c_778])).
% 3.23/1.61  tff(c_1064, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_755, c_1056])).
% 3.23/1.61  tff(c_1071, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_744, c_1064])).
% 3.23/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.61  
% 3.23/1.61  Inference rules
% 3.23/1.61  ----------------------
% 3.23/1.61  #Ref     : 1
% 3.23/1.61  #Sup     : 226
% 3.23/1.61  #Fact    : 0
% 3.23/1.61  #Define  : 0
% 3.23/1.61  #Split   : 11
% 3.23/1.61  #Chain   : 0
% 3.23/1.61  #Close   : 0
% 3.23/1.61  
% 3.23/1.61  Ordering : KBO
% 3.23/1.61  
% 3.23/1.61  Simplification rules
% 3.23/1.61  ----------------------
% 3.23/1.61  #Subsume      : 57
% 3.23/1.61  #Demod        : 74
% 3.23/1.61  #Tautology    : 58
% 3.23/1.61  #SimpNegUnit  : 15
% 3.23/1.61  #BackRed      : 15
% 3.23/1.61  
% 3.23/1.61  #Partial instantiations: 0
% 3.23/1.61  #Strategies tried      : 1
% 3.23/1.61  
% 3.23/1.61  Timing (in seconds)
% 3.23/1.61  ----------------------
% 3.60/1.61  Preprocessing        : 0.33
% 3.60/1.61  Parsing              : 0.16
% 3.60/1.61  CNF conversion       : 0.02
% 3.60/1.61  Main loop            : 0.52
% 3.60/1.61  Inferencing          : 0.18
% 3.60/1.61  Reduction            : 0.16
% 3.60/1.61  Demodulation         : 0.10
% 3.60/1.61  BG Simplification    : 0.02
% 3.60/1.61  Subsumption          : 0.11
% 3.60/1.61  Abstraction          : 0.02
% 3.60/1.61  MUC search           : 0.00
% 3.60/1.61  Cooper               : 0.00
% 3.60/1.61  Total                : 0.89
% 3.60/1.62  Index Insertion      : 0.00
% 3.60/1.62  Index Deletion       : 0.00
% 3.60/1.62  Index Matching       : 0.00
% 3.60/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
