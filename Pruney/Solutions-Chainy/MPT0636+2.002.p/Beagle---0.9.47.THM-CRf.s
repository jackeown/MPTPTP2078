%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:23 EST 2020

% Result     : Theorem 10.86s
% Output     : CNFRefutation 10.86s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 299 expanded)
%              Number of leaves         :   21 ( 117 expanded)
%              Depth                    :   18
%              Number of atoms          :  251 ( 862 expanded)
%              Number of equality atoms :    1 (  11 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,k6_relat_1(B))))
        <=> ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(D,k6_relat_1(C)))
      <=> ( r2_hidden(B,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(k6_relat_1(C),D))
      <=> ( r2_hidden(A,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_11] : v1_funct_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( v1_funct_1(k5_relat_1(A_9,B_10))
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k5_relat_1(A_9,B_10))
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,
    ( r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2'))))
    | r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_51,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,
    ( r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2'))))
    | r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_53,plain,(
    r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_28,plain,(
    ! [A_16,C_18] :
      ( r2_hidden(k4_tarski(A_16,k1_funct_1(C_18,A_16)),C_18)
      | ~ r2_hidden(A_16,k1_relat_1(C_18))
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_93,plain,(
    ! [A_49,B_50,D_51,C_52] :
      ( r2_hidden(k4_tarski(A_49,B_50),k5_relat_1(D_51,k6_relat_1(C_52)))
      | ~ r2_hidden(k4_tarski(A_49,B_50),D_51)
      | ~ r2_hidden(B_50,C_52)
      | ~ v1_relat_1(D_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [A_16,C_18,B_17] :
      ( r2_hidden(A_16,k1_relat_1(C_18))
      | ~ r2_hidden(k4_tarski(A_16,B_17),C_18)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4353,plain,(
    ! [A_396,D_397,C_398,B_399] :
      ( r2_hidden(A_396,k1_relat_1(k5_relat_1(D_397,k6_relat_1(C_398))))
      | ~ v1_funct_1(k5_relat_1(D_397,k6_relat_1(C_398)))
      | ~ v1_relat_1(k5_relat_1(D_397,k6_relat_1(C_398)))
      | ~ r2_hidden(k4_tarski(A_396,B_399),D_397)
      | ~ r2_hidden(B_399,C_398)
      | ~ v1_relat_1(D_397) ) ),
    inference(resolution,[status(thm)],[c_93,c_32])).

tff(c_14927,plain,(
    ! [A_616,C_617,C_618] :
      ( r2_hidden(A_616,k1_relat_1(k5_relat_1(C_617,k6_relat_1(C_618))))
      | ~ v1_funct_1(k5_relat_1(C_617,k6_relat_1(C_618)))
      | ~ v1_relat_1(k5_relat_1(C_617,k6_relat_1(C_618)))
      | ~ r2_hidden(k1_funct_1(C_617,A_616),C_618)
      | ~ r2_hidden(A_616,k1_relat_1(C_617))
      | ~ v1_funct_1(C_617)
      | ~ v1_relat_1(C_617) ) ),
    inference(resolution,[status(thm)],[c_28,c_4353])).

tff(c_38,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_55,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_53,c_38])).

tff(c_15068,plain,
    ( ~ v1_funct_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2')))
    | ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14927,c_55])).

tff(c_15136,plain,
    ( ~ v1_funct_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_51,c_53,c_15068])).

tff(c_15137,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_15136])).

tff(c_15140,plain,
    ( ~ v1_funct_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_15137])).

tff(c_15144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_18,c_20,c_15140])).

tff(c_15145,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_15136])).

tff(c_15154,plain,
    ( ~ v1_funct_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_15145])).

tff(c_15158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_18,c_20,c_15154])).

tff(c_15160,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_15159,plain,(
    r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_24,plain,(
    ! [C_15,A_12,B_13] :
      ( r2_hidden(k1_funct_1(C_15,A_12),k1_relat_1(B_13))
      | ~ r2_hidden(A_12,k1_relat_1(k5_relat_1(C_15,B_13)))
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_15425,plain,(
    ! [C_695,A_696,B_697] :
      ( r2_hidden(k1_funct_1(C_695,A_696),k1_relat_1(B_697))
      | ~ r2_hidden(A_696,k1_relat_1(k5_relat_1(C_695,B_697)))
      | ~ v1_funct_1(C_695)
      | ~ v1_relat_1(C_695)
      | ~ v1_funct_1(B_697)
      | ~ v1_relat_1(B_697) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_15239,plain,(
    ! [A_656,B_657,C_658,D_659] :
      ( r2_hidden(k4_tarski(A_656,B_657),k5_relat_1(k6_relat_1(C_658),D_659))
      | ~ r2_hidden(k4_tarski(A_656,B_657),D_659)
      | ~ r2_hidden(A_656,C_658)
      | ~ v1_relat_1(D_659) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_5,B_6,D_8,C_7] :
      ( r2_hidden(k4_tarski(A_5,B_6),D_8)
      | ~ r2_hidden(k4_tarski(A_5,B_6),k5_relat_1(D_8,k6_relat_1(C_7)))
      | ~ v1_relat_1(D_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_15243,plain,(
    ! [A_656,B_657,C_658,C_7] :
      ( r2_hidden(k4_tarski(A_656,B_657),k6_relat_1(C_658))
      | ~ v1_relat_1(k6_relat_1(C_658))
      | ~ r2_hidden(k4_tarski(A_656,B_657),k6_relat_1(C_7))
      | ~ r2_hidden(A_656,C_658)
      | ~ v1_relat_1(k6_relat_1(C_7)) ) ),
    inference(resolution,[status(thm)],[c_15239,c_10])).

tff(c_15309,plain,(
    ! [A_673,B_674,C_675,C_676] :
      ( r2_hidden(k4_tarski(A_673,B_674),k6_relat_1(C_675))
      | ~ r2_hidden(k4_tarski(A_673,B_674),k6_relat_1(C_676))
      | ~ r2_hidden(A_673,C_675) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_15243])).

tff(c_15312,plain,(
    ! [A_16,C_676,C_675] :
      ( r2_hidden(k4_tarski(A_16,k1_funct_1(k6_relat_1(C_676),A_16)),k6_relat_1(C_675))
      | ~ r2_hidden(A_16,C_675)
      | ~ r2_hidden(A_16,k1_relat_1(k6_relat_1(C_676)))
      | ~ v1_funct_1(k6_relat_1(C_676))
      | ~ v1_relat_1(k6_relat_1(C_676)) ) ),
    inference(resolution,[status(thm)],[c_28,c_15309])).

tff(c_15316,plain,(
    ! [A_677,C_678,C_679] :
      ( r2_hidden(k4_tarski(A_677,k1_funct_1(k6_relat_1(C_678),A_677)),k6_relat_1(C_679))
      | ~ r2_hidden(A_677,C_679)
      | ~ r2_hidden(A_677,k1_relat_1(k6_relat_1(C_678))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_15312])).

tff(c_15332,plain,(
    ! [A_677,C_679,C_678] :
      ( r2_hidden(A_677,k1_relat_1(k6_relat_1(C_679)))
      | ~ v1_funct_1(k6_relat_1(C_679))
      | ~ v1_relat_1(k6_relat_1(C_679))
      | ~ r2_hidden(A_677,C_679)
      | ~ r2_hidden(A_677,k1_relat_1(k6_relat_1(C_678))) ) ),
    inference(resolution,[status(thm)],[c_15316,c_32])).

tff(c_15343,plain,(
    ! [A_677,C_679,C_678] :
      ( r2_hidden(A_677,k1_relat_1(k6_relat_1(C_679)))
      | ~ r2_hidden(A_677,C_679)
      | ~ r2_hidden(A_677,k1_relat_1(k6_relat_1(C_678))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_15332])).

tff(c_15437,plain,(
    ! [C_695,A_696,C_679,C_678] :
      ( r2_hidden(k1_funct_1(C_695,A_696),k1_relat_1(k6_relat_1(C_679)))
      | ~ r2_hidden(k1_funct_1(C_695,A_696),C_679)
      | ~ r2_hidden(A_696,k1_relat_1(k5_relat_1(C_695,k6_relat_1(C_678))))
      | ~ v1_funct_1(C_695)
      | ~ v1_relat_1(C_695)
      | ~ v1_funct_1(k6_relat_1(C_678))
      | ~ v1_relat_1(k6_relat_1(C_678)) ) ),
    inference(resolution,[status(thm)],[c_15425,c_15343])).

tff(c_16049,plain,(
    ! [C_758,A_759,C_760,C_761] :
      ( r2_hidden(k1_funct_1(C_758,A_759),k1_relat_1(k6_relat_1(C_760)))
      | ~ r2_hidden(k1_funct_1(C_758,A_759),C_760)
      | ~ r2_hidden(A_759,k1_relat_1(k5_relat_1(C_758,k6_relat_1(C_761))))
      | ~ v1_funct_1(C_758)
      | ~ v1_relat_1(C_758) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_15437])).

tff(c_16057,plain,(
    ! [C_760] :
      ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),k1_relat_1(k6_relat_1(C_760)))
      | ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),C_760)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_15159,c_16049])).

tff(c_16063,plain,(
    ! [C_762] :
      ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),k1_relat_1(k6_relat_1(C_762)))
      | ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),C_762) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_16057])).

tff(c_12,plain,(
    ! [B_6,C_7,A_5,D_8] :
      ( r2_hidden(B_6,C_7)
      | ~ r2_hidden(k4_tarski(A_5,B_6),k5_relat_1(D_8,k6_relat_1(C_7)))
      | ~ v1_relat_1(D_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_15250,plain,(
    ! [B_657,C_7,C_658,A_656] :
      ( r2_hidden(B_657,C_7)
      | ~ v1_relat_1(k6_relat_1(C_658))
      | ~ r2_hidden(k4_tarski(A_656,B_657),k6_relat_1(C_7))
      | ~ r2_hidden(A_656,C_658)
      | ~ v1_relat_1(k6_relat_1(C_7)) ) ),
    inference(resolution,[status(thm)],[c_15239,c_12])).

tff(c_15270,plain,(
    ! [B_660,C_661,A_662,C_663] :
      ( r2_hidden(B_660,C_661)
      | ~ r2_hidden(k4_tarski(A_662,B_660),k6_relat_1(C_661))
      | ~ r2_hidden(A_662,C_663) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_15250])).

tff(c_15273,plain,(
    ! [C_661,A_16,C_663] :
      ( r2_hidden(k1_funct_1(k6_relat_1(C_661),A_16),C_661)
      | ~ r2_hidden(A_16,C_663)
      | ~ r2_hidden(A_16,k1_relat_1(k6_relat_1(C_661)))
      | ~ v1_funct_1(k6_relat_1(C_661))
      | ~ v1_relat_1(k6_relat_1(C_661)) ) ),
    inference(resolution,[status(thm)],[c_28,c_15270])).

tff(c_15276,plain,(
    ! [C_661,A_16,C_663] :
      ( r2_hidden(k1_funct_1(k6_relat_1(C_661),A_16),C_661)
      | ~ r2_hidden(A_16,C_663)
      | ~ r2_hidden(A_16,k1_relat_1(k6_relat_1(C_661))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_15273])).

tff(c_16081,plain,(
    ! [C_661,C_762] :
      ( r2_hidden(k1_funct_1(k6_relat_1(C_661),k1_funct_1('#skF_3','#skF_1')),C_661)
      | ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),k1_relat_1(k6_relat_1(C_661)))
      | ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),C_762) ) ),
    inference(resolution,[status(thm)],[c_16063,c_15276])).

tff(c_16146,plain,(
    ! [C_767] : ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),C_767) ),
    inference(splitLeft,[status(thm)],[c_16081])).

tff(c_16150,plain,(
    ! [B_13] :
      ( ~ r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',B_13)))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_24,c_16146])).

tff(c_16154,plain,(
    ! [B_768] :
      ( ~ r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',B_768)))
      | ~ v1_funct_1(B_768)
      | ~ v1_relat_1(B_768) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_16150])).

tff(c_16157,plain,
    ( ~ v1_funct_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_15159,c_16154])).

tff(c_16161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_16157])).

tff(c_16163,plain,(
    ! [C_769] :
      ( r2_hidden(k1_funct_1(k6_relat_1(C_769),k1_funct_1('#skF_3','#skF_1')),C_769)
      | ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),k1_relat_1(k6_relat_1(C_769))) ) ),
    inference(splitRight,[status(thm)],[c_16081])).

tff(c_15200,plain,(
    ! [A_645,B_646,D_647,C_648] :
      ( r2_hidden(k4_tarski(A_645,B_646),k5_relat_1(D_647,k6_relat_1(C_648)))
      | ~ r2_hidden(k4_tarski(A_645,B_646),D_647)
      | ~ r2_hidden(B_646,C_648)
      | ~ v1_relat_1(D_647) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k5_relat_1(k6_relat_1(C_3),D_4))
      | ~ v1_relat_1(D_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_15214,plain,(
    ! [A_645,C_3,C_648,B_646] :
      ( r2_hidden(A_645,C_3)
      | ~ v1_relat_1(k6_relat_1(C_648))
      | ~ r2_hidden(k4_tarski(A_645,B_646),k6_relat_1(C_3))
      | ~ r2_hidden(B_646,C_648)
      | ~ v1_relat_1(k6_relat_1(C_3)) ) ),
    inference(resolution,[status(thm)],[c_15200,c_6])).

tff(c_15231,plain,(
    ! [A_649,C_650,B_651,C_652] :
      ( r2_hidden(A_649,C_650)
      | ~ r2_hidden(k4_tarski(A_649,B_651),k6_relat_1(C_650))
      | ~ r2_hidden(B_651,C_652) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_15214])).

tff(c_15234,plain,(
    ! [A_16,C_650,C_652] :
      ( r2_hidden(A_16,C_650)
      | ~ r2_hidden(k1_funct_1(k6_relat_1(C_650),A_16),C_652)
      | ~ r2_hidden(A_16,k1_relat_1(k6_relat_1(C_650)))
      | ~ v1_funct_1(k6_relat_1(C_650))
      | ~ v1_relat_1(k6_relat_1(C_650)) ) ),
    inference(resolution,[status(thm)],[c_28,c_15231])).

tff(c_15237,plain,(
    ! [A_16,C_650,C_652] :
      ( r2_hidden(A_16,C_650)
      | ~ r2_hidden(k1_funct_1(k6_relat_1(C_650),A_16),C_652)
      | ~ r2_hidden(A_16,k1_relat_1(k6_relat_1(C_650))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_15234])).

tff(c_16225,plain,(
    ! [C_770] :
      ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),C_770)
      | ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),k1_relat_1(k6_relat_1(C_770))) ) ),
    inference(resolution,[status(thm)],[c_16163,c_15237])).

tff(c_16231,plain,(
    ! [C_770] :
      ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),C_770)
      | ~ r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',k6_relat_1(C_770))))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_relat_1(C_770))
      | ~ v1_relat_1(k6_relat_1(C_770)) ) ),
    inference(resolution,[status(thm)],[c_24,c_16225])).

tff(c_16236,plain,(
    ! [C_771] :
      ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),C_771)
      | ~ r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',k6_relat_1(C_771)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_36,c_34,c_16231])).

tff(c_16242,plain,(
    r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_15159,c_16236])).

tff(c_16247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15160,c_16242])).

tff(c_16249,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_16248,plain,(
    r2_hidden('#skF_1',k1_relat_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_16390,plain,(
    ! [A_824,C_825,B_826] :
      ( r2_hidden(A_824,k1_relat_1(C_825))
      | ~ r2_hidden(A_824,k1_relat_1(k5_relat_1(C_825,B_826)))
      | ~ v1_funct_1(C_825)
      | ~ v1_relat_1(C_825)
      | ~ v1_funct_1(B_826)
      | ~ v1_relat_1(B_826) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16401,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_16248,c_16390])).

tff(c_16406,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_36,c_34,c_16401])).

tff(c_16408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16249,c_16406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:37:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.86/3.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.86/3.89  
% 10.86/3.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.86/3.89  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 10.86/3.89  
% 10.86/3.89  %Foreground sorts:
% 10.86/3.89  
% 10.86/3.89  
% 10.86/3.89  %Background operators:
% 10.86/3.89  
% 10.86/3.89  
% 10.86/3.89  %Foreground operators:
% 10.86/3.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.86/3.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.86/3.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.86/3.89  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.86/3.89  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.86/3.89  tff('#skF_2', type, '#skF_2': $i).
% 10.86/3.89  tff('#skF_3', type, '#skF_3': $i).
% 10.86/3.89  tff('#skF_1', type, '#skF_1': $i).
% 10.86/3.89  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.86/3.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.86/3.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.86/3.89  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.86/3.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.86/3.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.86/3.89  
% 10.86/3.91  tff(f_93, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, k6_relat_1(B)))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_1)).
% 10.86/3.91  tff(f_57, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 10.86/3.91  tff(f_53, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 10.86/3.91  tff(f_82, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 10.86/3.91  tff(f_41, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(D, k6_relat_1(C))) <=> (r2_hidden(B, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_relat_1)).
% 10.86/3.91  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 10.86/3.91  tff(f_33, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(k6_relat_1(C), D)) <=> (r2_hidden(A, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_relat_1)).
% 10.86/3.91  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.86/3.91  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.86/3.91  tff(c_18, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.86/3.91  tff(c_20, plain, (![A_11]: (v1_funct_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.86/3.91  tff(c_14, plain, (![A_9, B_10]: (v1_funct_1(k5_relat_1(A_9, B_10)) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.86/3.91  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k5_relat_1(A_9, B_10)) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.86/3.91  tff(c_48, plain, (r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2')))) | r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.86/3.91  tff(c_51, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_48])).
% 10.86/3.91  tff(c_44, plain, (r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2')))) | r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.86/3.91  tff(c_53, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 10.86/3.91  tff(c_28, plain, (![A_16, C_18]: (r2_hidden(k4_tarski(A_16, k1_funct_1(C_18, A_16)), C_18) | ~r2_hidden(A_16, k1_relat_1(C_18)) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.86/3.91  tff(c_93, plain, (![A_49, B_50, D_51, C_52]: (r2_hidden(k4_tarski(A_49, B_50), k5_relat_1(D_51, k6_relat_1(C_52))) | ~r2_hidden(k4_tarski(A_49, B_50), D_51) | ~r2_hidden(B_50, C_52) | ~v1_relat_1(D_51))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.86/3.91  tff(c_32, plain, (![A_16, C_18, B_17]: (r2_hidden(A_16, k1_relat_1(C_18)) | ~r2_hidden(k4_tarski(A_16, B_17), C_18) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.86/3.91  tff(c_4353, plain, (![A_396, D_397, C_398, B_399]: (r2_hidden(A_396, k1_relat_1(k5_relat_1(D_397, k6_relat_1(C_398)))) | ~v1_funct_1(k5_relat_1(D_397, k6_relat_1(C_398))) | ~v1_relat_1(k5_relat_1(D_397, k6_relat_1(C_398))) | ~r2_hidden(k4_tarski(A_396, B_399), D_397) | ~r2_hidden(B_399, C_398) | ~v1_relat_1(D_397))), inference(resolution, [status(thm)], [c_93, c_32])).
% 10.86/3.91  tff(c_14927, plain, (![A_616, C_617, C_618]: (r2_hidden(A_616, k1_relat_1(k5_relat_1(C_617, k6_relat_1(C_618)))) | ~v1_funct_1(k5_relat_1(C_617, k6_relat_1(C_618))) | ~v1_relat_1(k5_relat_1(C_617, k6_relat_1(C_618))) | ~r2_hidden(k1_funct_1(C_617, A_616), C_618) | ~r2_hidden(A_616, k1_relat_1(C_617)) | ~v1_funct_1(C_617) | ~v1_relat_1(C_617))), inference(resolution, [status(thm)], [c_28, c_4353])).
% 10.86/3.91  tff(c_38, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.86/3.91  tff(c_55, plain, (~r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_53, c_38])).
% 10.86/3.91  tff(c_15068, plain, (~v1_funct_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2'))) | ~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14927, c_55])).
% 10.86/3.91  tff(c_15136, plain, (~v1_funct_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_51, c_53, c_15068])).
% 10.86/3.91  tff(c_15137, plain, (~v1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_15136])).
% 10.86/3.91  tff(c_15140, plain, (~v1_funct_1(k6_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_15137])).
% 10.86/3.91  tff(c_15144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_18, c_20, c_15140])).
% 10.86/3.91  tff(c_15145, plain, (~v1_funct_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_15136])).
% 10.86/3.91  tff(c_15154, plain, (~v1_funct_1(k6_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_15145])).
% 10.86/3.91  tff(c_15158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_18, c_20, c_15154])).
% 10.86/3.91  tff(c_15160, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 10.86/3.91  tff(c_15159, plain, (r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_44])).
% 10.86/3.91  tff(c_24, plain, (![C_15, A_12, B_13]: (r2_hidden(k1_funct_1(C_15, A_12), k1_relat_1(B_13)) | ~r2_hidden(A_12, k1_relat_1(k5_relat_1(C_15, B_13))) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.86/3.91  tff(c_15425, plain, (![C_695, A_696, B_697]: (r2_hidden(k1_funct_1(C_695, A_696), k1_relat_1(B_697)) | ~r2_hidden(A_696, k1_relat_1(k5_relat_1(C_695, B_697))) | ~v1_funct_1(C_695) | ~v1_relat_1(C_695) | ~v1_funct_1(B_697) | ~v1_relat_1(B_697))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.86/3.91  tff(c_15239, plain, (![A_656, B_657, C_658, D_659]: (r2_hidden(k4_tarski(A_656, B_657), k5_relat_1(k6_relat_1(C_658), D_659)) | ~r2_hidden(k4_tarski(A_656, B_657), D_659) | ~r2_hidden(A_656, C_658) | ~v1_relat_1(D_659))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.86/3.91  tff(c_10, plain, (![A_5, B_6, D_8, C_7]: (r2_hidden(k4_tarski(A_5, B_6), D_8) | ~r2_hidden(k4_tarski(A_5, B_6), k5_relat_1(D_8, k6_relat_1(C_7))) | ~v1_relat_1(D_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.86/3.91  tff(c_15243, plain, (![A_656, B_657, C_658, C_7]: (r2_hidden(k4_tarski(A_656, B_657), k6_relat_1(C_658)) | ~v1_relat_1(k6_relat_1(C_658)) | ~r2_hidden(k4_tarski(A_656, B_657), k6_relat_1(C_7)) | ~r2_hidden(A_656, C_658) | ~v1_relat_1(k6_relat_1(C_7)))), inference(resolution, [status(thm)], [c_15239, c_10])).
% 10.86/3.91  tff(c_15309, plain, (![A_673, B_674, C_675, C_676]: (r2_hidden(k4_tarski(A_673, B_674), k6_relat_1(C_675)) | ~r2_hidden(k4_tarski(A_673, B_674), k6_relat_1(C_676)) | ~r2_hidden(A_673, C_675))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_15243])).
% 10.86/3.91  tff(c_15312, plain, (![A_16, C_676, C_675]: (r2_hidden(k4_tarski(A_16, k1_funct_1(k6_relat_1(C_676), A_16)), k6_relat_1(C_675)) | ~r2_hidden(A_16, C_675) | ~r2_hidden(A_16, k1_relat_1(k6_relat_1(C_676))) | ~v1_funct_1(k6_relat_1(C_676)) | ~v1_relat_1(k6_relat_1(C_676)))), inference(resolution, [status(thm)], [c_28, c_15309])).
% 10.86/3.91  tff(c_15316, plain, (![A_677, C_678, C_679]: (r2_hidden(k4_tarski(A_677, k1_funct_1(k6_relat_1(C_678), A_677)), k6_relat_1(C_679)) | ~r2_hidden(A_677, C_679) | ~r2_hidden(A_677, k1_relat_1(k6_relat_1(C_678))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_15312])).
% 10.86/3.91  tff(c_15332, plain, (![A_677, C_679, C_678]: (r2_hidden(A_677, k1_relat_1(k6_relat_1(C_679))) | ~v1_funct_1(k6_relat_1(C_679)) | ~v1_relat_1(k6_relat_1(C_679)) | ~r2_hidden(A_677, C_679) | ~r2_hidden(A_677, k1_relat_1(k6_relat_1(C_678))))), inference(resolution, [status(thm)], [c_15316, c_32])).
% 10.86/3.91  tff(c_15343, plain, (![A_677, C_679, C_678]: (r2_hidden(A_677, k1_relat_1(k6_relat_1(C_679))) | ~r2_hidden(A_677, C_679) | ~r2_hidden(A_677, k1_relat_1(k6_relat_1(C_678))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_15332])).
% 10.86/3.91  tff(c_15437, plain, (![C_695, A_696, C_679, C_678]: (r2_hidden(k1_funct_1(C_695, A_696), k1_relat_1(k6_relat_1(C_679))) | ~r2_hidden(k1_funct_1(C_695, A_696), C_679) | ~r2_hidden(A_696, k1_relat_1(k5_relat_1(C_695, k6_relat_1(C_678)))) | ~v1_funct_1(C_695) | ~v1_relat_1(C_695) | ~v1_funct_1(k6_relat_1(C_678)) | ~v1_relat_1(k6_relat_1(C_678)))), inference(resolution, [status(thm)], [c_15425, c_15343])).
% 10.86/3.91  tff(c_16049, plain, (![C_758, A_759, C_760, C_761]: (r2_hidden(k1_funct_1(C_758, A_759), k1_relat_1(k6_relat_1(C_760))) | ~r2_hidden(k1_funct_1(C_758, A_759), C_760) | ~r2_hidden(A_759, k1_relat_1(k5_relat_1(C_758, k6_relat_1(C_761)))) | ~v1_funct_1(C_758) | ~v1_relat_1(C_758))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_15437])).
% 10.86/3.91  tff(c_16057, plain, (![C_760]: (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), k1_relat_1(k6_relat_1(C_760))) | ~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), C_760) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_15159, c_16049])).
% 10.86/3.91  tff(c_16063, plain, (![C_762]: (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), k1_relat_1(k6_relat_1(C_762))) | ~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), C_762))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_16057])).
% 10.86/3.91  tff(c_12, plain, (![B_6, C_7, A_5, D_8]: (r2_hidden(B_6, C_7) | ~r2_hidden(k4_tarski(A_5, B_6), k5_relat_1(D_8, k6_relat_1(C_7))) | ~v1_relat_1(D_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.86/3.91  tff(c_15250, plain, (![B_657, C_7, C_658, A_656]: (r2_hidden(B_657, C_7) | ~v1_relat_1(k6_relat_1(C_658)) | ~r2_hidden(k4_tarski(A_656, B_657), k6_relat_1(C_7)) | ~r2_hidden(A_656, C_658) | ~v1_relat_1(k6_relat_1(C_7)))), inference(resolution, [status(thm)], [c_15239, c_12])).
% 10.86/3.91  tff(c_15270, plain, (![B_660, C_661, A_662, C_663]: (r2_hidden(B_660, C_661) | ~r2_hidden(k4_tarski(A_662, B_660), k6_relat_1(C_661)) | ~r2_hidden(A_662, C_663))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_15250])).
% 10.86/3.91  tff(c_15273, plain, (![C_661, A_16, C_663]: (r2_hidden(k1_funct_1(k6_relat_1(C_661), A_16), C_661) | ~r2_hidden(A_16, C_663) | ~r2_hidden(A_16, k1_relat_1(k6_relat_1(C_661))) | ~v1_funct_1(k6_relat_1(C_661)) | ~v1_relat_1(k6_relat_1(C_661)))), inference(resolution, [status(thm)], [c_28, c_15270])).
% 10.86/3.91  tff(c_15276, plain, (![C_661, A_16, C_663]: (r2_hidden(k1_funct_1(k6_relat_1(C_661), A_16), C_661) | ~r2_hidden(A_16, C_663) | ~r2_hidden(A_16, k1_relat_1(k6_relat_1(C_661))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_15273])).
% 10.86/3.91  tff(c_16081, plain, (![C_661, C_762]: (r2_hidden(k1_funct_1(k6_relat_1(C_661), k1_funct_1('#skF_3', '#skF_1')), C_661) | ~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), k1_relat_1(k6_relat_1(C_661))) | ~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), C_762))), inference(resolution, [status(thm)], [c_16063, c_15276])).
% 10.86/3.91  tff(c_16146, plain, (![C_767]: (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), C_767))), inference(splitLeft, [status(thm)], [c_16081])).
% 10.86/3.91  tff(c_16150, plain, (![B_13]: (~r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', B_13))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_24, c_16146])).
% 10.86/3.91  tff(c_16154, plain, (![B_768]: (~r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', B_768))) | ~v1_funct_1(B_768) | ~v1_relat_1(B_768))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_16150])).
% 10.86/3.91  tff(c_16157, plain, (~v1_funct_1(k6_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_15159, c_16154])).
% 10.86/3.91  tff(c_16161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_16157])).
% 10.86/3.91  tff(c_16163, plain, (![C_769]: (r2_hidden(k1_funct_1(k6_relat_1(C_769), k1_funct_1('#skF_3', '#skF_1')), C_769) | ~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), k1_relat_1(k6_relat_1(C_769))))), inference(splitRight, [status(thm)], [c_16081])).
% 10.86/3.91  tff(c_15200, plain, (![A_645, B_646, D_647, C_648]: (r2_hidden(k4_tarski(A_645, B_646), k5_relat_1(D_647, k6_relat_1(C_648))) | ~r2_hidden(k4_tarski(A_645, B_646), D_647) | ~r2_hidden(B_646, C_648) | ~v1_relat_1(D_647))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.86/3.91  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k5_relat_1(k6_relat_1(C_3), D_4)) | ~v1_relat_1(D_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.86/3.91  tff(c_15214, plain, (![A_645, C_3, C_648, B_646]: (r2_hidden(A_645, C_3) | ~v1_relat_1(k6_relat_1(C_648)) | ~r2_hidden(k4_tarski(A_645, B_646), k6_relat_1(C_3)) | ~r2_hidden(B_646, C_648) | ~v1_relat_1(k6_relat_1(C_3)))), inference(resolution, [status(thm)], [c_15200, c_6])).
% 10.86/3.91  tff(c_15231, plain, (![A_649, C_650, B_651, C_652]: (r2_hidden(A_649, C_650) | ~r2_hidden(k4_tarski(A_649, B_651), k6_relat_1(C_650)) | ~r2_hidden(B_651, C_652))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_15214])).
% 10.86/3.91  tff(c_15234, plain, (![A_16, C_650, C_652]: (r2_hidden(A_16, C_650) | ~r2_hidden(k1_funct_1(k6_relat_1(C_650), A_16), C_652) | ~r2_hidden(A_16, k1_relat_1(k6_relat_1(C_650))) | ~v1_funct_1(k6_relat_1(C_650)) | ~v1_relat_1(k6_relat_1(C_650)))), inference(resolution, [status(thm)], [c_28, c_15231])).
% 10.86/3.91  tff(c_15237, plain, (![A_16, C_650, C_652]: (r2_hidden(A_16, C_650) | ~r2_hidden(k1_funct_1(k6_relat_1(C_650), A_16), C_652) | ~r2_hidden(A_16, k1_relat_1(k6_relat_1(C_650))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_15234])).
% 10.86/3.91  tff(c_16225, plain, (![C_770]: (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), C_770) | ~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), k1_relat_1(k6_relat_1(C_770))))), inference(resolution, [status(thm)], [c_16163, c_15237])).
% 10.86/3.91  tff(c_16231, plain, (![C_770]: (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), C_770) | ~r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', k6_relat_1(C_770)))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(k6_relat_1(C_770)) | ~v1_relat_1(k6_relat_1(C_770)))), inference(resolution, [status(thm)], [c_24, c_16225])).
% 10.86/3.91  tff(c_16236, plain, (![C_771]: (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), C_771) | ~r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', k6_relat_1(C_771)))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_36, c_34, c_16231])).
% 10.86/3.91  tff(c_16242, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_15159, c_16236])).
% 10.86/3.91  tff(c_16247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15160, c_16242])).
% 10.86/3.91  tff(c_16249, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_48])).
% 10.86/3.91  tff(c_16248, plain, (r2_hidden('#skF_1', k1_relat_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_48])).
% 10.86/3.91  tff(c_16390, plain, (![A_824, C_825, B_826]: (r2_hidden(A_824, k1_relat_1(C_825)) | ~r2_hidden(A_824, k1_relat_1(k5_relat_1(C_825, B_826))) | ~v1_funct_1(C_825) | ~v1_relat_1(C_825) | ~v1_funct_1(B_826) | ~v1_relat_1(B_826))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.86/3.91  tff(c_16401, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(k6_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_16248, c_16390])).
% 10.86/3.91  tff(c_16406, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_36, c_34, c_16401])).
% 10.86/3.91  tff(c_16408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16249, c_16406])).
% 10.86/3.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.86/3.91  
% 10.86/3.91  Inference rules
% 10.86/3.91  ----------------------
% 10.86/3.91  #Ref     : 0
% 10.86/3.91  #Sup     : 4214
% 10.86/3.91  #Fact    : 0
% 10.86/3.91  #Define  : 0
% 10.86/3.91  #Split   : 17
% 10.86/3.91  #Chain   : 0
% 10.86/3.91  #Close   : 0
% 10.86/3.91  
% 10.86/3.91  Ordering : KBO
% 10.86/3.91  
% 10.86/3.91  Simplification rules
% 10.86/3.91  ----------------------
% 10.86/3.91  #Subsume      : 2331
% 10.86/3.91  #Demod        : 978
% 10.86/3.91  #Tautology    : 196
% 10.86/3.91  #SimpNegUnit  : 153
% 10.86/3.91  #BackRed      : 15
% 10.86/3.91  
% 10.86/3.91  #Partial instantiations: 0
% 10.86/3.91  #Strategies tried      : 1
% 10.86/3.91  
% 10.86/3.91  Timing (in seconds)
% 10.86/3.91  ----------------------
% 10.86/3.91  Preprocessing        : 0.29
% 10.86/3.91  Parsing              : 0.16
% 10.86/3.91  CNF conversion       : 0.02
% 10.86/3.91  Main loop            : 2.86
% 10.86/3.91  Inferencing          : 0.74
% 10.86/3.91  Reduction            : 0.64
% 10.86/3.91  Demodulation         : 0.43
% 10.86/3.91  BG Simplification    : 0.09
% 10.86/3.91  Subsumption          : 1.22
% 10.86/3.91  Abstraction          : 0.14
% 10.86/3.91  MUC search           : 0.00
% 10.86/3.91  Cooper               : 0.00
% 10.86/3.91  Total                : 3.19
% 10.86/3.91  Index Insertion      : 0.00
% 10.86/3.91  Index Deletion       : 0.00
% 10.86/3.91  Index Matching       : 0.00
% 10.86/3.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
