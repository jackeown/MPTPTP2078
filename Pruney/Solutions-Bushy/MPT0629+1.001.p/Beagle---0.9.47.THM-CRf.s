%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0629+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:37 EST 2020

% Result     : Theorem 5.67s
% Output     : CNFRefutation 5.67s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 103 expanded)
%              Number of leaves         :   23 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  144 ( 407 expanded)
%              Number of equality atoms :    7 (  26 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( r2_hidden(A,k2_relat_1(k5_relat_1(C,B)))
             => r2_hidden(A,k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

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

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_22,plain,(
    ! [A_43,B_44] :
      ( v1_funct_1(k5_relat_1(A_43,B_44))
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_41,B_42] :
      ( v1_relat_1(k5_relat_1(A_41,B_42))
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    r2_hidden('#skF_5',k2_relat_1(k5_relat_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6,plain,(
    ! [A_1,C_37] :
      ( r2_hidden('#skF_4'(A_1,k2_relat_1(A_1),C_37),k1_relat_1(A_1))
      | ~ r2_hidden(C_37,k2_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [C_48,A_45,B_46] :
      ( r2_hidden(k1_funct_1(C_48,A_45),k1_relat_1(B_46))
      | ~ r2_hidden(A_45,k1_relat_1(k5_relat_1(C_48,B_46)))
      | ~ v1_funct_1(C_48)
      | ~ v1_relat_1(C_48)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_119,plain,(
    ! [C_82,B_83,A_84] :
      ( k1_funct_1(k5_relat_1(C_82,B_83),A_84) = k1_funct_1(B_83,k1_funct_1(C_82,A_84))
      | ~ r2_hidden(A_84,k1_relat_1(k5_relat_1(C_82,B_83)))
      | ~ v1_funct_1(C_82)
      | ~ v1_relat_1(C_82)
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_755,plain,(
    ! [C_171,B_172,C_173] :
      ( k1_funct_1(k5_relat_1(C_171,B_172),'#skF_4'(k5_relat_1(C_171,B_172),k2_relat_1(k5_relat_1(C_171,B_172)),C_173)) = k1_funct_1(B_172,k1_funct_1(C_171,'#skF_4'(k5_relat_1(C_171,B_172),k2_relat_1(k5_relat_1(C_171,B_172)),C_173)))
      | ~ v1_funct_1(C_171)
      | ~ v1_relat_1(C_171)
      | ~ v1_funct_1(B_172)
      | ~ v1_relat_1(B_172)
      | ~ r2_hidden(C_173,k2_relat_1(k5_relat_1(C_171,B_172)))
      | ~ v1_funct_1(k5_relat_1(C_171,B_172))
      | ~ v1_relat_1(k5_relat_1(C_171,B_172)) ) ),
    inference(resolution,[status(thm)],[c_6,c_119])).

tff(c_4,plain,(
    ! [A_1,C_37] :
      ( k1_funct_1(A_1,'#skF_4'(A_1,k2_relat_1(A_1),C_37)) = C_37
      | ~ r2_hidden(C_37,k2_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_868,plain,(
    ! [B_188,C_189,C_190] :
      ( k1_funct_1(B_188,k1_funct_1(C_189,'#skF_4'(k5_relat_1(C_189,B_188),k2_relat_1(k5_relat_1(C_189,B_188)),C_190))) = C_190
      | ~ r2_hidden(C_190,k2_relat_1(k5_relat_1(C_189,B_188)))
      | ~ v1_funct_1(k5_relat_1(C_189,B_188))
      | ~ v1_relat_1(k5_relat_1(C_189,B_188))
      | ~ v1_funct_1(C_189)
      | ~ v1_relat_1(C_189)
      | ~ v1_funct_1(B_188)
      | ~ v1_relat_1(B_188)
      | ~ r2_hidden(C_190,k2_relat_1(k5_relat_1(C_189,B_188)))
      | ~ v1_funct_1(k5_relat_1(C_189,B_188))
      | ~ v1_relat_1(k5_relat_1(C_189,B_188)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_4])).

tff(c_2,plain,(
    ! [A_1,D_40] :
      ( r2_hidden(k1_funct_1(A_1,D_40),k2_relat_1(A_1))
      | ~ r2_hidden(D_40,k1_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1579,plain,(
    ! [C_265,B_266,C_267] :
      ( r2_hidden(C_265,k2_relat_1(B_266))
      | ~ r2_hidden(k1_funct_1(C_267,'#skF_4'(k5_relat_1(C_267,B_266),k2_relat_1(k5_relat_1(C_267,B_266)),C_265)),k1_relat_1(B_266))
      | ~ v1_funct_1(B_266)
      | ~ v1_relat_1(B_266)
      | ~ r2_hidden(C_265,k2_relat_1(k5_relat_1(C_267,B_266)))
      | ~ v1_funct_1(k5_relat_1(C_267,B_266))
      | ~ v1_relat_1(k5_relat_1(C_267,B_266))
      | ~ v1_funct_1(C_267)
      | ~ v1_relat_1(C_267)
      | ~ v1_funct_1(B_266)
      | ~ v1_relat_1(B_266)
      | ~ r2_hidden(C_265,k2_relat_1(k5_relat_1(C_267,B_266)))
      | ~ v1_funct_1(k5_relat_1(C_267,B_266))
      | ~ v1_relat_1(k5_relat_1(C_267,B_266)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_2])).

tff(c_1585,plain,(
    ! [C_268,B_269,C_270] :
      ( r2_hidden(C_268,k2_relat_1(B_269))
      | ~ r2_hidden(C_268,k2_relat_1(k5_relat_1(C_270,B_269)))
      | ~ v1_funct_1(k5_relat_1(C_270,B_269))
      | ~ v1_relat_1(k5_relat_1(C_270,B_269))
      | ~ r2_hidden('#skF_4'(k5_relat_1(C_270,B_269),k2_relat_1(k5_relat_1(C_270,B_269)),C_268),k1_relat_1(k5_relat_1(C_270,B_269)))
      | ~ v1_funct_1(C_270)
      | ~ v1_relat_1(C_270)
      | ~ v1_funct_1(B_269)
      | ~ v1_relat_1(B_269) ) ),
    inference(resolution,[status(thm)],[c_28,c_1579])).

tff(c_1591,plain,(
    ! [C_271,B_272,C_273] :
      ( r2_hidden(C_271,k2_relat_1(B_272))
      | ~ v1_funct_1(C_273)
      | ~ v1_relat_1(C_273)
      | ~ v1_funct_1(B_272)
      | ~ v1_relat_1(B_272)
      | ~ r2_hidden(C_271,k2_relat_1(k5_relat_1(C_273,B_272)))
      | ~ v1_funct_1(k5_relat_1(C_273,B_272))
      | ~ v1_relat_1(k5_relat_1(C_273,B_272)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1585])).

tff(c_1663,plain,
    ( r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k5_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1(k5_relat_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_36,c_1591])).

tff(c_1684,plain,
    ( r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v1_funct_1(k5_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1(k5_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_1663])).

tff(c_1685,plain,
    ( ~ v1_funct_1(k5_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1(k5_relat_1('#skF_7','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1684])).

tff(c_1686,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1685])).

tff(c_1689,plain,
    ( ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_1686])).

tff(c_1693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_1689])).

tff(c_1694,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1685])).

tff(c_1698,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_1694])).

tff(c_1702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_44,c_42,c_1698])).

%------------------------------------------------------------------------------
