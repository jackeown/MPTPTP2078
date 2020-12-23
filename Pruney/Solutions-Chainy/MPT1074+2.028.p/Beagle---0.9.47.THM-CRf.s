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
% DateTime   : Thu Dec  3 10:18:10 EST 2020

% Result     : Theorem 20.00s
% Output     : CNFRefutation 20.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 129 expanded)
%              Number of leaves         :   26 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :  167 ( 397 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
          & ! [E] :
              ~ ( r2_hidden(E,A)
                & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_20,plain,(
    ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_42,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_24,c_34])).

tff(c_28,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_39,B_40] :
      ( ~ r2_hidden('#skF_1'(A_39,B_40),B_40)
      | r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    ! [A_48,B_49,C_50,D_51] :
      ( r2_hidden('#skF_2'(A_48,B_49,C_50,D_51),A_48)
      | ~ r2_hidden(C_50,k2_relset_1(A_48,B_49,D_51))
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(D_51,A_48,B_49)
      | ~ v1_funct_1(D_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_339,plain,(
    ! [A_115,B_116,C_117,A_118] :
      ( r2_hidden('#skF_2'(A_115,B_116,C_117,A_118),A_115)
      | ~ r2_hidden(C_117,k2_relset_1(A_115,B_116,A_118))
      | ~ v1_funct_2(A_118,A_115,B_116)
      | ~ v1_funct_1(A_118)
      | ~ r1_tarski(A_118,k2_zfmisc_1(A_115,B_116)) ) ),
    inference(resolution,[status(thm)],[c_10,c_66])).

tff(c_59,plain,(
    ! [A_45,C_46,B_47] :
      ( m1_subset_1(A_45,C_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(C_46))
      | ~ r2_hidden(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_64,plain,(
    ! [A_45,B_7,A_6] :
      ( m1_subset_1(A_45,B_7)
      | ~ r2_hidden(A_45,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_59])).

tff(c_705,plain,(
    ! [B_192,A_190,A_194,C_191,B_193] :
      ( m1_subset_1('#skF_2'(A_194,B_193,C_191,A_190),B_192)
      | ~ r1_tarski(A_194,B_192)
      | ~ r2_hidden(C_191,k2_relset_1(A_194,B_193,A_190))
      | ~ v1_funct_2(A_190,A_194,B_193)
      | ~ v1_funct_1(A_190)
      | ~ r1_tarski(A_190,k2_zfmisc_1(A_194,B_193)) ) ),
    inference(resolution,[status(thm)],[c_339,c_64])).

tff(c_733,plain,(
    ! [B_192,A_190,B_2,A_194,B_193] :
      ( m1_subset_1('#skF_2'(A_194,B_193,'#skF_1'(k2_relset_1(A_194,B_193,A_190),B_2),A_190),B_192)
      | ~ r1_tarski(A_194,B_192)
      | ~ v1_funct_2(A_190,A_194,B_193)
      | ~ v1_funct_1(A_190)
      | ~ r1_tarski(A_190,k2_zfmisc_1(A_194,B_193))
      | r1_tarski(k2_relset_1(A_194,B_193,A_190),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_705])).

tff(c_52,plain,(
    ! [C_42,B_43,A_44] :
      ( r2_hidden(C_42,B_43)
      | ~ r2_hidden(C_42,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_1,B_2,B_43] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_43)
      | ~ r1_tarski(A_1,B_43)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_232,plain,(
    ! [D_95,A_96,B_97,C_98] :
      ( k1_funct_1(D_95,'#skF_2'(A_96,B_97,C_98,D_95)) = C_98
      | ~ r2_hidden(C_98,k2_relset_1(A_96,B_97,D_95))
      | ~ m1_subset_1(D_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_2(D_95,A_96,B_97)
      | ~ v1_funct_1(D_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1275,plain,(
    ! [A_274,B_270,A_271,D_272,B_273] :
      ( k1_funct_1(D_272,'#skF_2'(A_271,B_270,'#skF_1'(A_274,B_273),D_272)) = '#skF_1'(A_274,B_273)
      | ~ m1_subset_1(D_272,k1_zfmisc_1(k2_zfmisc_1(A_271,B_270)))
      | ~ v1_funct_2(D_272,A_271,B_270)
      | ~ v1_funct_1(D_272)
      | ~ r1_tarski(A_274,k2_relset_1(A_271,B_270,D_272))
      | r1_tarski(A_274,B_273) ) ),
    inference(resolution,[status(thm)],[c_57,c_232])).

tff(c_1313,plain,(
    ! [A_274,B_270,A_271,A_6,B_273] :
      ( k1_funct_1(A_6,'#skF_2'(A_271,B_270,'#skF_1'(A_274,B_273),A_6)) = '#skF_1'(A_274,B_273)
      | ~ v1_funct_2(A_6,A_271,B_270)
      | ~ v1_funct_1(A_6)
      | ~ r1_tarski(A_274,k2_relset_1(A_271,B_270,A_6))
      | r1_tarski(A_274,B_273)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_271,B_270)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1275])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_71,plain,(
    ! [C_50] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_5',C_50,'#skF_6'),'#skF_4')
      | ~ r2_hidden(C_50,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_66])).

tff(c_118,plain,(
    ! [C_67] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_5',C_67,'#skF_6'),'#skF_4')
      | ~ r2_hidden(C_67,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_71])).

tff(c_219,plain,(
    ! [C_93,B_94] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5',C_93,'#skF_6'),B_94)
      | ~ r1_tarski('#skF_4',B_94)
      | ~ r2_hidden(C_93,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_118,c_64])).

tff(c_684,plain,(
    ! [A_187,B_188,B_189] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_1'(A_187,B_188),'#skF_6'),B_189)
      | ~ r1_tarski('#skF_4',B_189)
      | ~ r1_tarski(A_187,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_187,B_188) ) ),
    inference(resolution,[status(thm)],[c_57,c_219])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( k3_funct_2(A_11,B_12,C_13,D_14) = k1_funct_1(C_13,D_14)
      | ~ m1_subset_1(D_14,A_11)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_2(C_13,A_11,B_12)
      | ~ v1_funct_1(C_13)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_25086,plain,(
    ! [A_1782,C_1779,B_1781,B_1780,B_1783] :
      ( k3_funct_2(B_1781,B_1783,C_1779,'#skF_2'('#skF_4','#skF_5','#skF_1'(A_1782,B_1780),'#skF_6')) = k1_funct_1(C_1779,'#skF_2'('#skF_4','#skF_5','#skF_1'(A_1782,B_1780),'#skF_6'))
      | ~ m1_subset_1(C_1779,k1_zfmisc_1(k2_zfmisc_1(B_1781,B_1783)))
      | ~ v1_funct_2(C_1779,B_1781,B_1783)
      | ~ v1_funct_1(C_1779)
      | v1_xboole_0(B_1781)
      | ~ r1_tarski('#skF_4',B_1781)
      | ~ r1_tarski(A_1782,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_1782,B_1780) ) ),
    inference(resolution,[status(thm)],[c_684,c_14])).

tff(c_25205,plain,(
    ! [A_1782,B_1780] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_1782,B_1780),'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_1782,B_1780),'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4')
      | ~ r1_tarski('#skF_4','#skF_4')
      | ~ r1_tarski(A_1782,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_1782,B_1780) ) ),
    inference(resolution,[status(thm)],[c_24,c_25086])).

tff(c_25247,plain,(
    ! [A_1782,B_1780] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_1782,B_1780),'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_1782,B_1780),'#skF_6'))
      | v1_xboole_0('#skF_4')
      | ~ r1_tarski(A_1782,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_1782,B_1780) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_28,c_26,c_25205])).

tff(c_25249,plain,(
    ! [A_1784,B_1785] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_1784,B_1785),'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_1784,B_1785),'#skF_6'))
      | ~ r1_tarski(A_1784,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_1784,B_1785) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_25247])).

tff(c_22,plain,(
    ! [E_31] :
      ( r2_hidden(k3_funct_2('#skF_4','#skF_5','#skF_6',E_31),'#skF_3')
      | ~ m1_subset_1(E_31,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_25364,plain,(
    ! [A_1786,B_1787] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_1'(A_1786,B_1787),'#skF_6')),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_1'(A_1786,B_1787),'#skF_6'),'#skF_4')
      | ~ r1_tarski(A_1786,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_1786,B_1787) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25249,c_22])).

tff(c_25372,plain,(
    ! [A_274,B_273] :
      ( r2_hidden('#skF_1'(A_274,B_273),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_1'(A_274,B_273),'#skF_6'),'#skF_4')
      | ~ r1_tarski(A_274,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_274,B_273)
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | ~ r1_tarski(A_274,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_274,B_273)
      | ~ r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1313,c_25364])).

tff(c_25386,plain,(
    ! [A_1788,B_1789] :
      ( r2_hidden('#skF_1'(A_1788,B_1789),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_1'(A_1788,B_1789),'#skF_6'),'#skF_4')
      | ~ r1_tarski(A_1788,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | r1_tarski(A_1788,B_1789) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28,c_26,c_25372])).

tff(c_25394,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2),'#skF_3')
      | ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ r1_tarski('#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | ~ r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_2) ) ),
    inference(resolution,[status(thm)],[c_733,c_25386])).

tff(c_25438,plain,(
    ! [B_1792] :
      ( r2_hidden('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_1792),'#skF_3')
      | r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_1792) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28,c_26,c_50,c_50,c_25394])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_25446,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_25438,c_4])).

tff(c_25452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_20,c_25446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.00/12.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.00/12.05  
% 20.00/12.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.00/12.06  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 20.00/12.06  
% 20.00/12.06  %Foreground sorts:
% 20.00/12.06  
% 20.00/12.06  
% 20.00/12.06  %Background operators:
% 20.00/12.06  
% 20.00/12.06  
% 20.00/12.06  %Foreground operators:
% 20.00/12.06  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 20.00/12.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 20.00/12.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.00/12.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.00/12.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.00/12.06  tff('#skF_5', type, '#skF_5': $i).
% 20.00/12.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 20.00/12.06  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 20.00/12.06  tff('#skF_6', type, '#skF_6': $i).
% 20.00/12.06  tff('#skF_3', type, '#skF_3': $i).
% 20.00/12.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.00/12.06  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 20.00/12.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.00/12.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 20.00/12.06  tff('#skF_4', type, '#skF_4': $i).
% 20.00/12.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.00/12.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.00/12.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 20.00/12.06  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 20.00/12.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.00/12.06  
% 20.19/12.07  tff(f_92, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 20.19/12.07  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 20.19/12.07  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 20.19/12.07  tff(f_70, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 20.19/12.07  tff(f_42, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 20.19/12.07  tff(f_55, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 20.19/12.07  tff(c_20, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 20.19/12.07  tff(c_24, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 20.19/12.07  tff(c_34, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 20.19/12.07  tff(c_42, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_24, c_34])).
% 20.19/12.07  tff(c_28, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 20.19/12.07  tff(c_26, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 20.19/12.07  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.19/12.07  tff(c_45, plain, (![A_39, B_40]: (~r2_hidden('#skF_1'(A_39, B_40), B_40) | r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.19/12.07  tff(c_50, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_45])).
% 20.19/12.07  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 20.19/12.07  tff(c_66, plain, (![A_48, B_49, C_50, D_51]: (r2_hidden('#skF_2'(A_48, B_49, C_50, D_51), A_48) | ~r2_hidden(C_50, k2_relset_1(A_48, B_49, D_51)) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(D_51, A_48, B_49) | ~v1_funct_1(D_51))), inference(cnfTransformation, [status(thm)], [f_70])).
% 20.19/12.07  tff(c_339, plain, (![A_115, B_116, C_117, A_118]: (r2_hidden('#skF_2'(A_115, B_116, C_117, A_118), A_115) | ~r2_hidden(C_117, k2_relset_1(A_115, B_116, A_118)) | ~v1_funct_2(A_118, A_115, B_116) | ~v1_funct_1(A_118) | ~r1_tarski(A_118, k2_zfmisc_1(A_115, B_116)))), inference(resolution, [status(thm)], [c_10, c_66])).
% 20.19/12.07  tff(c_59, plain, (![A_45, C_46, B_47]: (m1_subset_1(A_45, C_46) | ~m1_subset_1(B_47, k1_zfmisc_1(C_46)) | ~r2_hidden(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_42])).
% 20.19/12.07  tff(c_64, plain, (![A_45, B_7, A_6]: (m1_subset_1(A_45, B_7) | ~r2_hidden(A_45, A_6) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_59])).
% 20.19/12.07  tff(c_705, plain, (![B_192, A_190, A_194, C_191, B_193]: (m1_subset_1('#skF_2'(A_194, B_193, C_191, A_190), B_192) | ~r1_tarski(A_194, B_192) | ~r2_hidden(C_191, k2_relset_1(A_194, B_193, A_190)) | ~v1_funct_2(A_190, A_194, B_193) | ~v1_funct_1(A_190) | ~r1_tarski(A_190, k2_zfmisc_1(A_194, B_193)))), inference(resolution, [status(thm)], [c_339, c_64])).
% 20.19/12.07  tff(c_733, plain, (![B_192, A_190, B_2, A_194, B_193]: (m1_subset_1('#skF_2'(A_194, B_193, '#skF_1'(k2_relset_1(A_194, B_193, A_190), B_2), A_190), B_192) | ~r1_tarski(A_194, B_192) | ~v1_funct_2(A_190, A_194, B_193) | ~v1_funct_1(A_190) | ~r1_tarski(A_190, k2_zfmisc_1(A_194, B_193)) | r1_tarski(k2_relset_1(A_194, B_193, A_190), B_2))), inference(resolution, [status(thm)], [c_6, c_705])).
% 20.19/12.07  tff(c_52, plain, (![C_42, B_43, A_44]: (r2_hidden(C_42, B_43) | ~r2_hidden(C_42, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.19/12.07  tff(c_57, plain, (![A_1, B_2, B_43]: (r2_hidden('#skF_1'(A_1, B_2), B_43) | ~r1_tarski(A_1, B_43) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_52])).
% 20.19/12.07  tff(c_232, plain, (![D_95, A_96, B_97, C_98]: (k1_funct_1(D_95, '#skF_2'(A_96, B_97, C_98, D_95))=C_98 | ~r2_hidden(C_98, k2_relset_1(A_96, B_97, D_95)) | ~m1_subset_1(D_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_2(D_95, A_96, B_97) | ~v1_funct_1(D_95))), inference(cnfTransformation, [status(thm)], [f_70])).
% 20.19/12.07  tff(c_1275, plain, (![A_274, B_270, A_271, D_272, B_273]: (k1_funct_1(D_272, '#skF_2'(A_271, B_270, '#skF_1'(A_274, B_273), D_272))='#skF_1'(A_274, B_273) | ~m1_subset_1(D_272, k1_zfmisc_1(k2_zfmisc_1(A_271, B_270))) | ~v1_funct_2(D_272, A_271, B_270) | ~v1_funct_1(D_272) | ~r1_tarski(A_274, k2_relset_1(A_271, B_270, D_272)) | r1_tarski(A_274, B_273))), inference(resolution, [status(thm)], [c_57, c_232])).
% 20.19/12.07  tff(c_1313, plain, (![A_274, B_270, A_271, A_6, B_273]: (k1_funct_1(A_6, '#skF_2'(A_271, B_270, '#skF_1'(A_274, B_273), A_6))='#skF_1'(A_274, B_273) | ~v1_funct_2(A_6, A_271, B_270) | ~v1_funct_1(A_6) | ~r1_tarski(A_274, k2_relset_1(A_271, B_270, A_6)) | r1_tarski(A_274, B_273) | ~r1_tarski(A_6, k2_zfmisc_1(A_271, B_270)))), inference(resolution, [status(thm)], [c_10, c_1275])).
% 20.19/12.07  tff(c_32, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 20.19/12.07  tff(c_71, plain, (![C_50]: (r2_hidden('#skF_2'('#skF_4', '#skF_5', C_50, '#skF_6'), '#skF_4') | ~r2_hidden(C_50, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_24, c_66])).
% 20.19/12.07  tff(c_118, plain, (![C_67]: (r2_hidden('#skF_2'('#skF_4', '#skF_5', C_67, '#skF_6'), '#skF_4') | ~r2_hidden(C_67, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_71])).
% 20.19/12.07  tff(c_219, plain, (![C_93, B_94]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', C_93, '#skF_6'), B_94) | ~r1_tarski('#skF_4', B_94) | ~r2_hidden(C_93, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_118, c_64])).
% 20.19/12.07  tff(c_684, plain, (![A_187, B_188, B_189]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_187, B_188), '#skF_6'), B_189) | ~r1_tarski('#skF_4', B_189) | ~r1_tarski(A_187, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_187, B_188))), inference(resolution, [status(thm)], [c_57, c_219])).
% 20.19/12.07  tff(c_14, plain, (![A_11, B_12, C_13, D_14]: (k3_funct_2(A_11, B_12, C_13, D_14)=k1_funct_1(C_13, D_14) | ~m1_subset_1(D_14, A_11) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_2(C_13, A_11, B_12) | ~v1_funct_1(C_13) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 20.19/12.07  tff(c_25086, plain, (![A_1782, C_1779, B_1781, B_1780, B_1783]: (k3_funct_2(B_1781, B_1783, C_1779, '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1782, B_1780), '#skF_6'))=k1_funct_1(C_1779, '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1782, B_1780), '#skF_6')) | ~m1_subset_1(C_1779, k1_zfmisc_1(k2_zfmisc_1(B_1781, B_1783))) | ~v1_funct_2(C_1779, B_1781, B_1783) | ~v1_funct_1(C_1779) | v1_xboole_0(B_1781) | ~r1_tarski('#skF_4', B_1781) | ~r1_tarski(A_1782, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_1782, B_1780))), inference(resolution, [status(thm)], [c_684, c_14])).
% 20.19/12.07  tff(c_25205, plain, (![A_1782, B_1780]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1782, B_1780), '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1782, B_1780), '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4') | ~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski(A_1782, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_1782, B_1780))), inference(resolution, [status(thm)], [c_24, c_25086])).
% 20.19/12.07  tff(c_25247, plain, (![A_1782, B_1780]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1782, B_1780), '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1782, B_1780), '#skF_6')) | v1_xboole_0('#skF_4') | ~r1_tarski(A_1782, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_1782, B_1780))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_28, c_26, c_25205])).
% 20.19/12.07  tff(c_25249, plain, (![A_1784, B_1785]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1784, B_1785), '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1784, B_1785), '#skF_6')) | ~r1_tarski(A_1784, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_1784, B_1785))), inference(negUnitSimplification, [status(thm)], [c_32, c_25247])).
% 20.19/12.07  tff(c_22, plain, (![E_31]: (r2_hidden(k3_funct_2('#skF_4', '#skF_5', '#skF_6', E_31), '#skF_3') | ~m1_subset_1(E_31, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 20.19/12.07  tff(c_25364, plain, (![A_1786, B_1787]: (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1786, B_1787), '#skF_6')), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1786, B_1787), '#skF_6'), '#skF_4') | ~r1_tarski(A_1786, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_1786, B_1787))), inference(superposition, [status(thm), theory('equality')], [c_25249, c_22])).
% 20.19/12.07  tff(c_25372, plain, (![A_274, B_273]: (r2_hidden('#skF_1'(A_274, B_273), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_274, B_273), '#skF_6'), '#skF_4') | ~r1_tarski(A_274, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_274, B_273) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | ~r1_tarski(A_274, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_274, B_273) | ~r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1313, c_25364])).
% 20.19/12.07  tff(c_25386, plain, (![A_1788, B_1789]: (r2_hidden('#skF_1'(A_1788, B_1789), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_1'(A_1788, B_1789), '#skF_6'), '#skF_4') | ~r1_tarski(A_1788, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | r1_tarski(A_1788, B_1789))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_28, c_26, c_25372])).
% 20.19/12.07  tff(c_25394, plain, (![B_2]: (r2_hidden('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2), '#skF_3') | ~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | ~r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_2))), inference(resolution, [status(thm)], [c_733, c_25386])).
% 20.19/12.07  tff(c_25438, plain, (![B_1792]: (r2_hidden('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_1792), '#skF_3') | r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_1792))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_28, c_26, c_50, c_50, c_25394])).
% 20.19/12.07  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.19/12.07  tff(c_25446, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_25438, c_4])).
% 20.19/12.07  tff(c_25452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_20, c_25446])).
% 20.19/12.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.19/12.07  
% 20.19/12.07  Inference rules
% 20.19/12.07  ----------------------
% 20.19/12.07  #Ref     : 0
% 20.19/12.07  #Sup     : 6613
% 20.19/12.07  #Fact    : 0
% 20.19/12.07  #Define  : 0
% 20.19/12.07  #Split   : 44
% 20.19/12.07  #Chain   : 0
% 20.19/12.07  #Close   : 0
% 20.19/12.07  
% 20.19/12.07  Ordering : KBO
% 20.19/12.07  
% 20.19/12.07  Simplification rules
% 20.19/12.07  ----------------------
% 20.19/12.07  #Subsume      : 588
% 20.19/12.07  #Demod        : 218
% 20.19/12.07  #Tautology    : 97
% 20.19/12.07  #SimpNegUnit  : 20
% 20.19/12.07  #BackRed      : 0
% 20.19/12.07  
% 20.19/12.07  #Partial instantiations: 0
% 20.19/12.07  #Strategies tried      : 1
% 20.19/12.07  
% 20.19/12.07  Timing (in seconds)
% 20.19/12.07  ----------------------
% 20.22/12.07  Preprocessing        : 0.32
% 20.22/12.07  Parsing              : 0.18
% 20.22/12.07  CNF conversion       : 0.02
% 20.22/12.07  Main loop            : 10.96
% 20.22/12.07  Inferencing          : 1.21
% 20.22/12.07  Reduction            : 1.38
% 20.22/12.08  Demodulation         : 0.89
% 20.22/12.08  BG Simplification    : 0.18
% 20.22/12.08  Subsumption          : 7.66
% 20.22/12.08  Abstraction          : 0.31
% 20.22/12.08  MUC search           : 0.00
% 20.22/12.08  Cooper               : 0.00
% 20.22/12.08  Total                : 11.31
% 20.22/12.08  Index Insertion      : 0.00
% 20.22/12.08  Index Deletion       : 0.00
% 20.22/12.08  Index Matching       : 0.00
% 20.22/12.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
