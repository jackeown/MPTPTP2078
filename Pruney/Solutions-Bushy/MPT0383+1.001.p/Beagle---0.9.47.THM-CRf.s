%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0383+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:13 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   44 (  68 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 166 expanded)
%              Number of equality atoms :    7 (  19 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(D,C)
          & r1_tarski(C,k2_zfmisc_1(A,B))
          & ! [E] :
              ( m1_subset_1(E,A)
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => D != k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
        & r2_hidden(D,A)
        & ! [E,F] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_20,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_55,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( r2_hidden('#skF_1'(A_29,B_30,C_31,D_32),B_30)
      | ~ r2_hidden(D_32,A_29)
      | ~ r1_tarski(A_29,k2_zfmisc_1(B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( ~ v1_xboole_0(B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_64,plain,(
    ! [B_33,D_34,A_35,C_36] :
      ( ~ v1_xboole_0(B_33)
      | ~ r2_hidden(D_34,A_35)
      | ~ r1_tarski(A_35,k2_zfmisc_1(B_33,C_36)) ) ),
    inference(resolution,[status(thm)],[c_55,c_16])).

tff(c_74,plain,(
    ! [B_37,C_38] :
      ( ~ v1_xboole_0(B_37)
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(B_37,C_38)) ) ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_74])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( m1_subset_1(B_2,A_1)
      | ~ r2_hidden(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_157,plain,(
    ! [A_90,B_91,C_92,D_93] :
      ( m1_subset_1('#skF_1'(A_90,B_91,C_92,D_93),B_91)
      | v1_xboole_0(B_91)
      | ~ r2_hidden(D_93,A_90)
      | ~ r1_tarski(A_90,k2_zfmisc_1(B_91,C_92)) ) ),
    inference(resolution,[status(thm)],[c_55,c_2])).

tff(c_159,plain,(
    ! [D_93] :
      ( m1_subset_1('#skF_1'('#skF_5','#skF_3','#skF_4',D_93),'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ r2_hidden(D_93,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_157])).

tff(c_162,plain,(
    ! [D_93] :
      ( m1_subset_1('#skF_1'('#skF_5','#skF_3','#skF_4',D_93),'#skF_3')
      | ~ r2_hidden(D_93,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_159])).

tff(c_84,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( r2_hidden('#skF_2'(A_43,B_44,C_45,D_46),C_45)
      | ~ r2_hidden(D_46,A_43)
      | ~ r1_tarski(A_43,k2_zfmisc_1(B_44,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_96,plain,(
    ! [C_47,D_48,A_49,B_50] :
      ( ~ v1_xboole_0(C_47)
      | ~ r2_hidden(D_48,A_49)
      | ~ r1_tarski(A_49,k2_zfmisc_1(B_50,C_47)) ) ),
    inference(resolution,[status(thm)],[c_84,c_16])).

tff(c_109,plain,(
    ! [C_51,B_52] :
      ( ~ v1_xboole_0(C_51)
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(B_52,C_51)) ) ),
    inference(resolution,[status(thm)],[c_22,c_96])).

tff(c_113,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_109])).

tff(c_146,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( m1_subset_1('#skF_2'(A_85,B_86,C_87,D_88),C_87)
      | v1_xboole_0(C_87)
      | ~ r2_hidden(D_88,A_85)
      | ~ r1_tarski(A_85,k2_zfmisc_1(B_86,C_87)) ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_148,plain,(
    ! [D_88] :
      ( m1_subset_1('#skF_2'('#skF_5','#skF_3','#skF_4',D_88),'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ r2_hidden(D_88,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_146])).

tff(c_151,plain,(
    ! [D_88] :
      ( m1_subset_1('#skF_2'('#skF_5','#skF_3','#skF_4',D_88),'#skF_4')
      | ~ r2_hidden(D_88,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_148])).

tff(c_114,plain,(
    ! [A_53,B_54,C_55,D_56] :
      ( k4_tarski('#skF_1'(A_53,B_54,C_55,D_56),'#skF_2'(A_53,B_54,C_55,D_56)) = D_56
      | ~ r2_hidden(D_56,A_53)
      | ~ r1_tarski(A_53,k2_zfmisc_1(B_54,C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [E_14,F_16] :
      ( k4_tarski(E_14,F_16) != '#skF_6'
      | ~ m1_subset_1(F_16,'#skF_4')
      | ~ m1_subset_1(E_14,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_169,plain,(
    ! [D_95,A_96,B_97,C_98] :
      ( D_95 != '#skF_6'
      | ~ m1_subset_1('#skF_2'(A_96,B_97,C_98,D_95),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_96,B_97,C_98,D_95),'#skF_3')
      | ~ r2_hidden(D_95,A_96)
      | ~ r1_tarski(A_96,k2_zfmisc_1(B_97,C_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_18])).

tff(c_171,plain,(
    ! [D_88] :
      ( D_88 != '#skF_6'
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_3','#skF_4',D_88),'#skF_3')
      | ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(D_88,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_151,c_169])).

tff(c_180,plain,(
    ! [D_99] :
      ( D_99 != '#skF_6'
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_3','#skF_4',D_99),'#skF_3')
      | ~ r2_hidden(D_99,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_171])).

tff(c_189,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_162,c_180])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_22])).

%------------------------------------------------------------------------------
