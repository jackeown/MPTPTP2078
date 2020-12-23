%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:17 EST 2020

% Result     : Theorem 7.44s
% Output     : CNFRefutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 456 expanded)
%              Number of leaves         :   44 ( 187 expanded)
%              Depth                    :   12
%              Number of atoms          :  586 (2523 expanded)
%              Number of equality atoms :   98 ( 439 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(k1_tmap_1,type,(
    k1_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_237,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( ~ v1_xboole_0(C)
                  & m1_subset_1(C,k1_zfmisc_1(A)) )
               => ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & m1_subset_1(D,k1_zfmisc_1(A)) )
                   => ( r1_subset_1(C,D)
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,C,B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,D,B)
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                             => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),C) = E
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),D) = F ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_195,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & m1_subset_1(C,k1_zfmisc_1(A))
        & ~ v1_xboole_0(D)
        & m1_subset_1(D,k1_zfmisc_1(A))
        & v1_funct_1(E)
        & v1_funct_2(E,C,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,D,B)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
     => ( v1_funct_1(k1_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k1_tmap_1(A,B,C,D,E,F),k4_subset_1(A,C,D),B)
        & m1_subset_1(k1_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_161,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & m1_subset_1(C,k1_zfmisc_1(A)) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,C,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,D,B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                         => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,k4_subset_1(A,C,D),B)
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) )
                               => ( G = k1_tmap_1(A,B,C,D,E,F)
                                <=> ( k2_partfun1(k4_subset_1(A,C,D),B,G,C) = E
                                    & k2_partfun1(k4_subset_1(A,C,D),B,G,D) = F ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_87,plain,(
    ! [C_232,A_233,B_234] :
      ( v1_relat_1(C_232)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_95,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_87])).

tff(c_12,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_379,plain,(
    ! [A_290,B_291] :
      ( r2_hidden('#skF_1'(A_290,B_291),A_290)
      | r1_xboole_0(A_290,B_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_389,plain,(
    ! [A_294,B_295] :
      ( ~ r1_tarski(A_294,'#skF_1'(A_294,B_295))
      | r1_xboole_0(A_294,B_295) ) ),
    inference(resolution,[status(thm)],[c_379,c_22])).

tff(c_394,plain,(
    ! [B_295] : r1_xboole_0(k1_xboole_0,B_295) ),
    inference(resolution,[status(thm)],[c_12,c_389])).

tff(c_496,plain,(
    ! [A_317,B_318] :
      ( k7_relat_1(A_317,B_318) = k1_xboole_0
      | ~ r1_xboole_0(B_318,k1_relat_1(A_317))
      | ~ v1_relat_1(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_507,plain,(
    ! [A_319] :
      ( k7_relat_1(A_319,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_319) ) ),
    inference(resolution,[status(thm)],[c_394,c_496])).

tff(c_514,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_507])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_94,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_87])).

tff(c_515,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94,c_507])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_66,plain,(
    r1_subset_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_3420,plain,(
    ! [A_792,B_793] :
      ( r1_xboole_0(A_792,B_793)
      | ~ r1_subset_1(A_792,B_793)
      | v1_xboole_0(B_793)
      | v1_xboole_0(A_792) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4153,plain,(
    ! [A_883,B_884] :
      ( k3_xboole_0(A_883,B_884) = k1_xboole_0
      | ~ r1_subset_1(A_883,B_884)
      | v1_xboole_0(B_884)
      | v1_xboole_0(A_883) ) ),
    inference(resolution,[status(thm)],[c_3420,c_2])).

tff(c_4156,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_4153])).

tff(c_4159,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_70,c_4156])).

tff(c_3448,plain,(
    ! [A_797,B_798,C_799] :
      ( k9_subset_1(A_797,B_798,C_799) = k3_xboole_0(B_798,C_799)
      | ~ m1_subset_1(C_799,k1_zfmisc_1(A_797)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3459,plain,(
    ! [B_798] : k9_subset_1('#skF_2',B_798,'#skF_5') = k3_xboole_0(B_798,'#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_3448])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_62,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_56,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_4353,plain,(
    ! [F_907,D_908,B_906,A_909,E_910,C_911] :
      ( v1_funct_1(k1_tmap_1(A_909,B_906,C_911,D_908,E_910,F_907))
      | ~ m1_subset_1(F_907,k1_zfmisc_1(k2_zfmisc_1(D_908,B_906)))
      | ~ v1_funct_2(F_907,D_908,B_906)
      | ~ v1_funct_1(F_907)
      | ~ m1_subset_1(E_910,k1_zfmisc_1(k2_zfmisc_1(C_911,B_906)))
      | ~ v1_funct_2(E_910,C_911,B_906)
      | ~ v1_funct_1(E_910)
      | ~ m1_subset_1(D_908,k1_zfmisc_1(A_909))
      | v1_xboole_0(D_908)
      | ~ m1_subset_1(C_911,k1_zfmisc_1(A_909))
      | v1_xboole_0(C_911)
      | v1_xboole_0(B_906)
      | v1_xboole_0(A_909) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_4355,plain,(
    ! [A_909,C_911,E_910] :
      ( v1_funct_1(k1_tmap_1(A_909,'#skF_3',C_911,'#skF_5',E_910,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_910,k1_zfmisc_1(k2_zfmisc_1(C_911,'#skF_3')))
      | ~ v1_funct_2(E_910,C_911,'#skF_3')
      | ~ v1_funct_1(E_910)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_909))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_911,k1_zfmisc_1(A_909))
      | v1_xboole_0(C_911)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_909) ) ),
    inference(resolution,[status(thm)],[c_54,c_4353])).

tff(c_4360,plain,(
    ! [A_909,C_911,E_910] :
      ( v1_funct_1(k1_tmap_1(A_909,'#skF_3',C_911,'#skF_5',E_910,'#skF_7'))
      | ~ m1_subset_1(E_910,k1_zfmisc_1(k2_zfmisc_1(C_911,'#skF_3')))
      | ~ v1_funct_2(E_910,C_911,'#skF_3')
      | ~ v1_funct_1(E_910)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_909))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_911,k1_zfmisc_1(A_909))
      | v1_xboole_0(C_911)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_909) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_4355])).

tff(c_4403,plain,(
    ! [A_919,C_920,E_921] :
      ( v1_funct_1(k1_tmap_1(A_919,'#skF_3',C_920,'#skF_5',E_921,'#skF_7'))
      | ~ m1_subset_1(E_921,k1_zfmisc_1(k2_zfmisc_1(C_920,'#skF_3')))
      | ~ v1_funct_2(E_921,C_920,'#skF_3')
      | ~ v1_funct_1(E_921)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_919))
      | ~ m1_subset_1(C_920,k1_zfmisc_1(A_919))
      | v1_xboole_0(C_920)
      | v1_xboole_0(A_919) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_4360])).

tff(c_4407,plain,(
    ! [A_919] :
      ( v1_funct_1(k1_tmap_1(A_919,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_919))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_919))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_919) ) ),
    inference(resolution,[status(thm)],[c_60,c_4403])).

tff(c_4414,plain,(
    ! [A_919] :
      ( v1_funct_1(k1_tmap_1(A_919,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_919))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_919))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_919) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_4407])).

tff(c_4490,plain,(
    ! [A_945] :
      ( v1_funct_1(k1_tmap_1(A_945,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_945))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_945))
      | v1_xboole_0(A_945) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4414])).

tff(c_4493,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_4490])).

tff(c_4496,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4493])).

tff(c_4497,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4496])).

tff(c_4088,plain,(
    ! [A_874,B_875,C_876,D_877] :
      ( k2_partfun1(A_874,B_875,C_876,D_877) = k7_relat_1(C_876,D_877)
      | ~ m1_subset_1(C_876,k1_zfmisc_1(k2_zfmisc_1(A_874,B_875)))
      | ~ v1_funct_1(C_876) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4092,plain,(
    ! [D_877] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_877) = k7_relat_1('#skF_6',D_877)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60,c_4088])).

tff(c_4098,plain,(
    ! [D_877] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_877) = k7_relat_1('#skF_6',D_877) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4092])).

tff(c_4090,plain,(
    ! [D_877] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_877) = k7_relat_1('#skF_7',D_877)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_54,c_4088])).

tff(c_4095,plain,(
    ! [D_877] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_877) = k7_relat_1('#skF_7',D_877) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4090])).

tff(c_48,plain,(
    ! [E_166,F_167,B_163,D_165,A_162,C_164] :
      ( v1_funct_2(k1_tmap_1(A_162,B_163,C_164,D_165,E_166,F_167),k4_subset_1(A_162,C_164,D_165),B_163)
      | ~ m1_subset_1(F_167,k1_zfmisc_1(k2_zfmisc_1(D_165,B_163)))
      | ~ v1_funct_2(F_167,D_165,B_163)
      | ~ v1_funct_1(F_167)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(C_164,B_163)))
      | ~ v1_funct_2(E_166,C_164,B_163)
      | ~ v1_funct_1(E_166)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(A_162))
      | v1_xboole_0(D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(A_162))
      | v1_xboole_0(C_164)
      | v1_xboole_0(B_163)
      | v1_xboole_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_46,plain,(
    ! [E_166,F_167,B_163,D_165,A_162,C_164] :
      ( m1_subset_1(k1_tmap_1(A_162,B_163,C_164,D_165,E_166,F_167),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_162,C_164,D_165),B_163)))
      | ~ m1_subset_1(F_167,k1_zfmisc_1(k2_zfmisc_1(D_165,B_163)))
      | ~ v1_funct_2(F_167,D_165,B_163)
      | ~ v1_funct_1(F_167)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(C_164,B_163)))
      | ~ v1_funct_2(E_166,C_164,B_163)
      | ~ v1_funct_1(E_166)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(A_162))
      | v1_xboole_0(D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(A_162))
      | v1_xboole_0(C_164)
      | v1_xboole_0(B_163)
      | v1_xboole_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_4728,plain,(
    ! [F_972,A_973,B_975,E_974,D_976,C_977] :
      ( k2_partfun1(k4_subset_1(A_973,C_977,D_976),B_975,k1_tmap_1(A_973,B_975,C_977,D_976,E_974,F_972),C_977) = E_974
      | ~ m1_subset_1(k1_tmap_1(A_973,B_975,C_977,D_976,E_974,F_972),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_973,C_977,D_976),B_975)))
      | ~ v1_funct_2(k1_tmap_1(A_973,B_975,C_977,D_976,E_974,F_972),k4_subset_1(A_973,C_977,D_976),B_975)
      | ~ v1_funct_1(k1_tmap_1(A_973,B_975,C_977,D_976,E_974,F_972))
      | k2_partfun1(D_976,B_975,F_972,k9_subset_1(A_973,C_977,D_976)) != k2_partfun1(C_977,B_975,E_974,k9_subset_1(A_973,C_977,D_976))
      | ~ m1_subset_1(F_972,k1_zfmisc_1(k2_zfmisc_1(D_976,B_975)))
      | ~ v1_funct_2(F_972,D_976,B_975)
      | ~ v1_funct_1(F_972)
      | ~ m1_subset_1(E_974,k1_zfmisc_1(k2_zfmisc_1(C_977,B_975)))
      | ~ v1_funct_2(E_974,C_977,B_975)
      | ~ v1_funct_1(E_974)
      | ~ m1_subset_1(D_976,k1_zfmisc_1(A_973))
      | v1_xboole_0(D_976)
      | ~ m1_subset_1(C_977,k1_zfmisc_1(A_973))
      | v1_xboole_0(C_977)
      | v1_xboole_0(B_975)
      | v1_xboole_0(A_973) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_5429,plain,(
    ! [D_1115,F_1114,B_1113,A_1116,C_1118,E_1117] :
      ( k2_partfun1(k4_subset_1(A_1116,C_1118,D_1115),B_1113,k1_tmap_1(A_1116,B_1113,C_1118,D_1115,E_1117,F_1114),C_1118) = E_1117
      | ~ v1_funct_2(k1_tmap_1(A_1116,B_1113,C_1118,D_1115,E_1117,F_1114),k4_subset_1(A_1116,C_1118,D_1115),B_1113)
      | ~ v1_funct_1(k1_tmap_1(A_1116,B_1113,C_1118,D_1115,E_1117,F_1114))
      | k2_partfun1(D_1115,B_1113,F_1114,k9_subset_1(A_1116,C_1118,D_1115)) != k2_partfun1(C_1118,B_1113,E_1117,k9_subset_1(A_1116,C_1118,D_1115))
      | ~ m1_subset_1(F_1114,k1_zfmisc_1(k2_zfmisc_1(D_1115,B_1113)))
      | ~ v1_funct_2(F_1114,D_1115,B_1113)
      | ~ v1_funct_1(F_1114)
      | ~ m1_subset_1(E_1117,k1_zfmisc_1(k2_zfmisc_1(C_1118,B_1113)))
      | ~ v1_funct_2(E_1117,C_1118,B_1113)
      | ~ v1_funct_1(E_1117)
      | ~ m1_subset_1(D_1115,k1_zfmisc_1(A_1116))
      | v1_xboole_0(D_1115)
      | ~ m1_subset_1(C_1118,k1_zfmisc_1(A_1116))
      | v1_xboole_0(C_1118)
      | v1_xboole_0(B_1113)
      | v1_xboole_0(A_1116) ) ),
    inference(resolution,[status(thm)],[c_46,c_4728])).

tff(c_5683,plain,(
    ! [F_1157,B_1156,D_1158,A_1159,C_1161,E_1160] :
      ( k2_partfun1(k4_subset_1(A_1159,C_1161,D_1158),B_1156,k1_tmap_1(A_1159,B_1156,C_1161,D_1158,E_1160,F_1157),C_1161) = E_1160
      | ~ v1_funct_1(k1_tmap_1(A_1159,B_1156,C_1161,D_1158,E_1160,F_1157))
      | k2_partfun1(D_1158,B_1156,F_1157,k9_subset_1(A_1159,C_1161,D_1158)) != k2_partfun1(C_1161,B_1156,E_1160,k9_subset_1(A_1159,C_1161,D_1158))
      | ~ m1_subset_1(F_1157,k1_zfmisc_1(k2_zfmisc_1(D_1158,B_1156)))
      | ~ v1_funct_2(F_1157,D_1158,B_1156)
      | ~ v1_funct_1(F_1157)
      | ~ m1_subset_1(E_1160,k1_zfmisc_1(k2_zfmisc_1(C_1161,B_1156)))
      | ~ v1_funct_2(E_1160,C_1161,B_1156)
      | ~ v1_funct_1(E_1160)
      | ~ m1_subset_1(D_1158,k1_zfmisc_1(A_1159))
      | v1_xboole_0(D_1158)
      | ~ m1_subset_1(C_1161,k1_zfmisc_1(A_1159))
      | v1_xboole_0(C_1161)
      | v1_xboole_0(B_1156)
      | v1_xboole_0(A_1159) ) ),
    inference(resolution,[status(thm)],[c_48,c_5429])).

tff(c_5687,plain,(
    ! [A_1159,C_1161,E_1160] :
      ( k2_partfun1(k4_subset_1(A_1159,C_1161,'#skF_5'),'#skF_3',k1_tmap_1(A_1159,'#skF_3',C_1161,'#skF_5',E_1160,'#skF_7'),C_1161) = E_1160
      | ~ v1_funct_1(k1_tmap_1(A_1159,'#skF_3',C_1161,'#skF_5',E_1160,'#skF_7'))
      | k2_partfun1(C_1161,'#skF_3',E_1160,k9_subset_1(A_1159,C_1161,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_1159,C_1161,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1160,k1_zfmisc_1(k2_zfmisc_1(C_1161,'#skF_3')))
      | ~ v1_funct_2(E_1160,C_1161,'#skF_3')
      | ~ v1_funct_1(E_1160)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1159))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1161,k1_zfmisc_1(A_1159))
      | v1_xboole_0(C_1161)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1159) ) ),
    inference(resolution,[status(thm)],[c_54,c_5683])).

tff(c_5693,plain,(
    ! [A_1159,C_1161,E_1160] :
      ( k2_partfun1(k4_subset_1(A_1159,C_1161,'#skF_5'),'#skF_3',k1_tmap_1(A_1159,'#skF_3',C_1161,'#skF_5',E_1160,'#skF_7'),C_1161) = E_1160
      | ~ v1_funct_1(k1_tmap_1(A_1159,'#skF_3',C_1161,'#skF_5',E_1160,'#skF_7'))
      | k2_partfun1(C_1161,'#skF_3',E_1160,k9_subset_1(A_1159,C_1161,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1159,C_1161,'#skF_5'))
      | ~ m1_subset_1(E_1160,k1_zfmisc_1(k2_zfmisc_1(C_1161,'#skF_3')))
      | ~ v1_funct_2(E_1160,C_1161,'#skF_3')
      | ~ v1_funct_1(E_1160)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1159))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1161,k1_zfmisc_1(A_1159))
      | v1_xboole_0(C_1161)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_4095,c_5687])).

tff(c_5999,plain,(
    ! [A_1218,C_1219,E_1220] :
      ( k2_partfun1(k4_subset_1(A_1218,C_1219,'#skF_5'),'#skF_3',k1_tmap_1(A_1218,'#skF_3',C_1219,'#skF_5',E_1220,'#skF_7'),C_1219) = E_1220
      | ~ v1_funct_1(k1_tmap_1(A_1218,'#skF_3',C_1219,'#skF_5',E_1220,'#skF_7'))
      | k2_partfun1(C_1219,'#skF_3',E_1220,k9_subset_1(A_1218,C_1219,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1218,C_1219,'#skF_5'))
      | ~ m1_subset_1(E_1220,k1_zfmisc_1(k2_zfmisc_1(C_1219,'#skF_3')))
      | ~ v1_funct_2(E_1220,C_1219,'#skF_3')
      | ~ v1_funct_1(E_1220)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1218))
      | ~ m1_subset_1(C_1219,k1_zfmisc_1(A_1218))
      | v1_xboole_0(C_1219)
      | v1_xboole_0(A_1218) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_5693])).

tff(c_6006,plain,(
    ! [A_1218] :
      ( k2_partfun1(k4_subset_1(A_1218,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1218,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1218,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_1218,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1218,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1218))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1218))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1218) ) ),
    inference(resolution,[status(thm)],[c_60,c_5999])).

tff(c_6016,plain,(
    ! [A_1218] :
      ( k2_partfun1(k4_subset_1(A_1218,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1218,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1218,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1218,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1218,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1218))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1218))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_4098,c_6006])).

tff(c_6078,plain,(
    ! [A_1226] :
      ( k2_partfun1(k4_subset_1(A_1226,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1226,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1226,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1226,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1226,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1226))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1226))
      | v1_xboole_0(A_1226) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_6016])).

tff(c_541,plain,(
    ! [A_323,B_324] :
      ( r1_xboole_0(A_323,B_324)
      | ~ r1_subset_1(A_323,B_324)
      | v1_xboole_0(B_324)
      | v1_xboole_0(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1480,plain,(
    ! [A_443,B_444] :
      ( k3_xboole_0(A_443,B_444) = k1_xboole_0
      | ~ r1_subset_1(A_443,B_444)
      | v1_xboole_0(B_444)
      | v1_xboole_0(A_443) ) ),
    inference(resolution,[status(thm)],[c_541,c_2])).

tff(c_1483,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1480])).

tff(c_1486,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_70,c_1483])).

tff(c_565,plain,(
    ! [A_328,B_329,C_330] :
      ( k9_subset_1(A_328,B_329,C_330) = k3_xboole_0(B_329,C_330)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(A_328)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_576,plain,(
    ! [B_329] : k9_subset_1('#skF_2',B_329,'#skF_5') = k3_xboole_0(B_329,'#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_565])).

tff(c_1762,plain,(
    ! [B_481,F_482,C_486,E_485,D_483,A_484] :
      ( v1_funct_1(k1_tmap_1(A_484,B_481,C_486,D_483,E_485,F_482))
      | ~ m1_subset_1(F_482,k1_zfmisc_1(k2_zfmisc_1(D_483,B_481)))
      | ~ v1_funct_2(F_482,D_483,B_481)
      | ~ v1_funct_1(F_482)
      | ~ m1_subset_1(E_485,k1_zfmisc_1(k2_zfmisc_1(C_486,B_481)))
      | ~ v1_funct_2(E_485,C_486,B_481)
      | ~ v1_funct_1(E_485)
      | ~ m1_subset_1(D_483,k1_zfmisc_1(A_484))
      | v1_xboole_0(D_483)
      | ~ m1_subset_1(C_486,k1_zfmisc_1(A_484))
      | v1_xboole_0(C_486)
      | v1_xboole_0(B_481)
      | v1_xboole_0(A_484) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_1764,plain,(
    ! [A_484,C_486,E_485] :
      ( v1_funct_1(k1_tmap_1(A_484,'#skF_3',C_486,'#skF_5',E_485,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_485,k1_zfmisc_1(k2_zfmisc_1(C_486,'#skF_3')))
      | ~ v1_funct_2(E_485,C_486,'#skF_3')
      | ~ v1_funct_1(E_485)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_484))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_486,k1_zfmisc_1(A_484))
      | v1_xboole_0(C_486)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_484) ) ),
    inference(resolution,[status(thm)],[c_54,c_1762])).

tff(c_1769,plain,(
    ! [A_484,C_486,E_485] :
      ( v1_funct_1(k1_tmap_1(A_484,'#skF_3',C_486,'#skF_5',E_485,'#skF_7'))
      | ~ m1_subset_1(E_485,k1_zfmisc_1(k2_zfmisc_1(C_486,'#skF_3')))
      | ~ v1_funct_2(E_485,C_486,'#skF_3')
      | ~ v1_funct_1(E_485)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_484))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_486,k1_zfmisc_1(A_484))
      | v1_xboole_0(C_486)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_484) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1764])).

tff(c_2119,plain,(
    ! [A_550,C_551,E_552] :
      ( v1_funct_1(k1_tmap_1(A_550,'#skF_3',C_551,'#skF_5',E_552,'#skF_7'))
      | ~ m1_subset_1(E_552,k1_zfmisc_1(k2_zfmisc_1(C_551,'#skF_3')))
      | ~ v1_funct_2(E_552,C_551,'#skF_3')
      | ~ v1_funct_1(E_552)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_550))
      | ~ m1_subset_1(C_551,k1_zfmisc_1(A_550))
      | v1_xboole_0(C_551)
      | v1_xboole_0(A_550) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_1769])).

tff(c_2126,plain,(
    ! [A_550] :
      ( v1_funct_1(k1_tmap_1(A_550,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_550))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_550))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_550) ) ),
    inference(resolution,[status(thm)],[c_60,c_2119])).

tff(c_2136,plain,(
    ! [A_550] :
      ( v1_funct_1(k1_tmap_1(A_550,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_550))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_550))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_550) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2126])).

tff(c_2145,plain,(
    ! [A_554] :
      ( v1_funct_1(k1_tmap_1(A_554,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_554))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_554))
      | v1_xboole_0(A_554) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2136])).

tff(c_2148,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_2145])).

tff(c_2151,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2148])).

tff(c_2152,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2151])).

tff(c_1571,plain,(
    ! [A_456,B_457,C_458,D_459] :
      ( k2_partfun1(A_456,B_457,C_458,D_459) = k7_relat_1(C_458,D_459)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(A_456,B_457)))
      | ~ v1_funct_1(C_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1575,plain,(
    ! [D_459] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_459) = k7_relat_1('#skF_6',D_459)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60,c_1571])).

tff(c_1581,plain,(
    ! [D_459] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_459) = k7_relat_1('#skF_6',D_459) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1575])).

tff(c_1573,plain,(
    ! [D_459] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_459) = k7_relat_1('#skF_7',D_459)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_54,c_1571])).

tff(c_1578,plain,(
    ! [D_459] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_459) = k7_relat_1('#skF_7',D_459) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1573])).

tff(c_2195,plain,(
    ! [B_568,F_565,A_566,D_569,E_567,C_570] :
      ( k2_partfun1(k4_subset_1(A_566,C_570,D_569),B_568,k1_tmap_1(A_566,B_568,C_570,D_569,E_567,F_565),D_569) = F_565
      | ~ m1_subset_1(k1_tmap_1(A_566,B_568,C_570,D_569,E_567,F_565),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_566,C_570,D_569),B_568)))
      | ~ v1_funct_2(k1_tmap_1(A_566,B_568,C_570,D_569,E_567,F_565),k4_subset_1(A_566,C_570,D_569),B_568)
      | ~ v1_funct_1(k1_tmap_1(A_566,B_568,C_570,D_569,E_567,F_565))
      | k2_partfun1(D_569,B_568,F_565,k9_subset_1(A_566,C_570,D_569)) != k2_partfun1(C_570,B_568,E_567,k9_subset_1(A_566,C_570,D_569))
      | ~ m1_subset_1(F_565,k1_zfmisc_1(k2_zfmisc_1(D_569,B_568)))
      | ~ v1_funct_2(F_565,D_569,B_568)
      | ~ v1_funct_1(F_565)
      | ~ m1_subset_1(E_567,k1_zfmisc_1(k2_zfmisc_1(C_570,B_568)))
      | ~ v1_funct_2(E_567,C_570,B_568)
      | ~ v1_funct_1(E_567)
      | ~ m1_subset_1(D_569,k1_zfmisc_1(A_566))
      | v1_xboole_0(D_569)
      | ~ m1_subset_1(C_570,k1_zfmisc_1(A_566))
      | v1_xboole_0(C_570)
      | v1_xboole_0(B_568)
      | v1_xboole_0(A_566) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_2820,plain,(
    ! [F_695,E_698,C_699,A_697,D_696,B_694] :
      ( k2_partfun1(k4_subset_1(A_697,C_699,D_696),B_694,k1_tmap_1(A_697,B_694,C_699,D_696,E_698,F_695),D_696) = F_695
      | ~ v1_funct_2(k1_tmap_1(A_697,B_694,C_699,D_696,E_698,F_695),k4_subset_1(A_697,C_699,D_696),B_694)
      | ~ v1_funct_1(k1_tmap_1(A_697,B_694,C_699,D_696,E_698,F_695))
      | k2_partfun1(D_696,B_694,F_695,k9_subset_1(A_697,C_699,D_696)) != k2_partfun1(C_699,B_694,E_698,k9_subset_1(A_697,C_699,D_696))
      | ~ m1_subset_1(F_695,k1_zfmisc_1(k2_zfmisc_1(D_696,B_694)))
      | ~ v1_funct_2(F_695,D_696,B_694)
      | ~ v1_funct_1(F_695)
      | ~ m1_subset_1(E_698,k1_zfmisc_1(k2_zfmisc_1(C_699,B_694)))
      | ~ v1_funct_2(E_698,C_699,B_694)
      | ~ v1_funct_1(E_698)
      | ~ m1_subset_1(D_696,k1_zfmisc_1(A_697))
      | v1_xboole_0(D_696)
      | ~ m1_subset_1(C_699,k1_zfmisc_1(A_697))
      | v1_xboole_0(C_699)
      | v1_xboole_0(B_694)
      | v1_xboole_0(A_697) ) ),
    inference(resolution,[status(thm)],[c_46,c_2195])).

tff(c_3023,plain,(
    ! [B_736,A_739,C_741,E_740,D_738,F_737] :
      ( k2_partfun1(k4_subset_1(A_739,C_741,D_738),B_736,k1_tmap_1(A_739,B_736,C_741,D_738,E_740,F_737),D_738) = F_737
      | ~ v1_funct_1(k1_tmap_1(A_739,B_736,C_741,D_738,E_740,F_737))
      | k2_partfun1(D_738,B_736,F_737,k9_subset_1(A_739,C_741,D_738)) != k2_partfun1(C_741,B_736,E_740,k9_subset_1(A_739,C_741,D_738))
      | ~ m1_subset_1(F_737,k1_zfmisc_1(k2_zfmisc_1(D_738,B_736)))
      | ~ v1_funct_2(F_737,D_738,B_736)
      | ~ v1_funct_1(F_737)
      | ~ m1_subset_1(E_740,k1_zfmisc_1(k2_zfmisc_1(C_741,B_736)))
      | ~ v1_funct_2(E_740,C_741,B_736)
      | ~ v1_funct_1(E_740)
      | ~ m1_subset_1(D_738,k1_zfmisc_1(A_739))
      | v1_xboole_0(D_738)
      | ~ m1_subset_1(C_741,k1_zfmisc_1(A_739))
      | v1_xboole_0(C_741)
      | v1_xboole_0(B_736)
      | v1_xboole_0(A_739) ) ),
    inference(resolution,[status(thm)],[c_48,c_2820])).

tff(c_3027,plain,(
    ! [A_739,C_741,E_740] :
      ( k2_partfun1(k4_subset_1(A_739,C_741,'#skF_5'),'#skF_3',k1_tmap_1(A_739,'#skF_3',C_741,'#skF_5',E_740,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_739,'#skF_3',C_741,'#skF_5',E_740,'#skF_7'))
      | k2_partfun1(C_741,'#skF_3',E_740,k9_subset_1(A_739,C_741,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_739,C_741,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_740,k1_zfmisc_1(k2_zfmisc_1(C_741,'#skF_3')))
      | ~ v1_funct_2(E_740,C_741,'#skF_3')
      | ~ v1_funct_1(E_740)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_739))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_741,k1_zfmisc_1(A_739))
      | v1_xboole_0(C_741)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_739) ) ),
    inference(resolution,[status(thm)],[c_54,c_3023])).

tff(c_3033,plain,(
    ! [A_739,C_741,E_740] :
      ( k2_partfun1(k4_subset_1(A_739,C_741,'#skF_5'),'#skF_3',k1_tmap_1(A_739,'#skF_3',C_741,'#skF_5',E_740,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_739,'#skF_3',C_741,'#skF_5',E_740,'#skF_7'))
      | k2_partfun1(C_741,'#skF_3',E_740,k9_subset_1(A_739,C_741,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_739,C_741,'#skF_5'))
      | ~ m1_subset_1(E_740,k1_zfmisc_1(k2_zfmisc_1(C_741,'#skF_3')))
      | ~ v1_funct_2(E_740,C_741,'#skF_3')
      | ~ v1_funct_1(E_740)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_739))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_741,k1_zfmisc_1(A_739))
      | v1_xboole_0(C_741)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_739) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1578,c_3027])).

tff(c_3318,plain,(
    ! [A_784,C_785,E_786] :
      ( k2_partfun1(k4_subset_1(A_784,C_785,'#skF_5'),'#skF_3',k1_tmap_1(A_784,'#skF_3',C_785,'#skF_5',E_786,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_784,'#skF_3',C_785,'#skF_5',E_786,'#skF_7'))
      | k2_partfun1(C_785,'#skF_3',E_786,k9_subset_1(A_784,C_785,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_784,C_785,'#skF_5'))
      | ~ m1_subset_1(E_786,k1_zfmisc_1(k2_zfmisc_1(C_785,'#skF_3')))
      | ~ v1_funct_2(E_786,C_785,'#skF_3')
      | ~ v1_funct_1(E_786)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_784))
      | ~ m1_subset_1(C_785,k1_zfmisc_1(A_784))
      | v1_xboole_0(C_785)
      | v1_xboole_0(A_784) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_3033])).

tff(c_3325,plain,(
    ! [A_784] :
      ( k2_partfun1(k4_subset_1(A_784,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_784,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_784,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_784,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_784,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_784))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_784))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_784) ) ),
    inference(resolution,[status(thm)],[c_60,c_3318])).

tff(c_3335,plain,(
    ! [A_784] :
      ( k2_partfun1(k4_subset_1(A_784,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_784,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_784,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_784,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_784,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_784))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_784))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_784) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1581,c_3325])).

tff(c_3390,plain,(
    ! [A_791] :
      ( k2_partfun1(k4_subset_1(A_791,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_791,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_791,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_791,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_791,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_791))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_791))
      | v1_xboole_0(A_791) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3335])).

tff(c_102,plain,(
    ! [A_237,B_238] :
      ( r2_hidden('#skF_1'(A_237,B_238),A_237)
      | r1_xboole_0(A_237,B_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_142,plain,(
    ! [A_248,B_249] :
      ( ~ r1_tarski(A_248,'#skF_1'(A_248,B_249))
      | r1_xboole_0(A_248,B_249) ) ),
    inference(resolution,[status(thm)],[c_102,c_22])).

tff(c_147,plain,(
    ! [B_249] : r1_xboole_0(k1_xboole_0,B_249) ),
    inference(resolution,[status(thm)],[c_12,c_142])).

tff(c_190,plain,(
    ! [A_258,B_259] :
      ( k7_relat_1(A_258,B_259) = k1_xboole_0
      | ~ r1_xboole_0(B_259,k1_relat_1(A_258))
      | ~ v1_relat_1(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_201,plain,(
    ! [A_260] :
      ( k7_relat_1(A_260,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_260) ) ),
    inference(resolution,[status(thm)],[c_147,c_190])).

tff(c_208,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_201])).

tff(c_346,plain,(
    ! [A_284,B_285,C_286,D_287] :
      ( k2_partfun1(A_284,B_285,C_286,D_287) = k7_relat_1(C_286,D_287)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285)))
      | ~ v1_funct_1(C_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_350,plain,(
    ! [D_287] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_287) = k7_relat_1('#skF_6',D_287)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60,c_346])).

tff(c_356,plain,(
    ! [D_287] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_287) = k7_relat_1('#skF_6',D_287) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_350])).

tff(c_209,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94,c_201])).

tff(c_348,plain,(
    ! [D_287] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_287) = k7_relat_1('#skF_7',D_287)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_54,c_346])).

tff(c_353,plain,(
    ! [D_287] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_287) = k7_relat_1('#skF_7',D_287) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_348])).

tff(c_218,plain,(
    ! [A_261,B_262] :
      ( r1_xboole_0(A_261,B_262)
      | ~ r1_subset_1(A_261,B_262)
      | v1_xboole_0(B_262)
      | v1_xboole_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_330,plain,(
    ! [A_282,B_283] :
      ( k3_xboole_0(A_282,B_283) = k1_xboole_0
      | ~ r1_subset_1(A_282,B_283)
      | v1_xboole_0(B_283)
      | v1_xboole_0(A_282) ) ),
    inference(resolution,[status(thm)],[c_218,c_2])).

tff(c_336,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_330])).

tff(c_340,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_70,c_336])).

tff(c_251,plain,(
    ! [A_266,B_267,C_268] :
      ( k9_subset_1(A_266,B_267,C_268) = k3_xboole_0(B_267,C_268)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(A_266)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_262,plain,(
    ! [B_267] : k9_subset_1('#skF_2',B_267,'#skF_5') = k3_xboole_0(B_267,'#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_251])).

tff(c_52,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_96,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_264,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_262,c_96])).

tff(c_341,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k1_xboole_0) != k2_partfun1('#skF_4','#skF_3','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_340,c_264])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_356,c_209,c_353,c_341])).

tff(c_377,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_540,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_377])).

tff(c_3401,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3390,c_540])).

tff(c_3415,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_514,c_515,c_1486,c_576,c_1486,c_576,c_2152,c_3401])).

tff(c_3417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3415])).

tff(c_3418,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_377])).

tff(c_6087,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6078,c_3418])).

tff(c_6098,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_514,c_515,c_4159,c_3459,c_4159,c_3459,c_4497,c_6087])).

tff(c_6100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6098])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.44/2.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.57/2.84  
% 7.57/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.57/2.85  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.57/2.85  
% 7.57/2.85  %Foreground sorts:
% 7.57/2.85  
% 7.57/2.85  
% 7.57/2.85  %Background operators:
% 7.57/2.85  
% 7.57/2.85  
% 7.57/2.85  %Foreground operators:
% 7.57/2.85  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 7.57/2.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.57/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.57/2.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.57/2.85  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.57/2.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.57/2.85  tff('#skF_7', type, '#skF_7': $i).
% 7.57/2.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.57/2.85  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.57/2.85  tff('#skF_5', type, '#skF_5': $i).
% 7.57/2.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.57/2.85  tff('#skF_6', type, '#skF_6': $i).
% 7.57/2.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.57/2.85  tff('#skF_2', type, '#skF_2': $i).
% 7.57/2.85  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.57/2.85  tff('#skF_3', type, '#skF_3': $i).
% 7.57/2.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.57/2.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.57/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.57/2.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.57/2.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.57/2.85  tff('#skF_4', type, '#skF_4': $i).
% 7.57/2.85  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.57/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.57/2.85  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.57/2.85  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.57/2.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.57/2.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.57/2.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.57/2.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.57/2.85  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.57/2.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.57/2.85  
% 7.57/2.87  tff(f_237, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 7.57/2.87  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.57/2.87  tff(f_49, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.57/2.87  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.57/2.87  tff(f_75, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.57/2.87  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 7.57/2.87  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 7.57/2.87  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.57/2.87  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.57/2.87  tff(f_195, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 7.57/2.87  tff(f_113, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.57/2.87  tff(f_161, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 7.57/2.87  tff(c_78, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 7.57/2.87  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 7.57/2.87  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 7.57/2.87  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_237])).
% 7.57/2.87  tff(c_87, plain, (![C_232, A_233, B_234]: (v1_relat_1(C_232) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.57/2.87  tff(c_95, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_87])).
% 7.57/2.87  tff(c_12, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.57/2.87  tff(c_379, plain, (![A_290, B_291]: (r2_hidden('#skF_1'(A_290, B_291), A_290) | r1_xboole_0(A_290, B_291))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.57/2.87  tff(c_22, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.57/2.87  tff(c_389, plain, (![A_294, B_295]: (~r1_tarski(A_294, '#skF_1'(A_294, B_295)) | r1_xboole_0(A_294, B_295))), inference(resolution, [status(thm)], [c_379, c_22])).
% 7.57/2.87  tff(c_394, plain, (![B_295]: (r1_xboole_0(k1_xboole_0, B_295))), inference(resolution, [status(thm)], [c_12, c_389])).
% 7.57/2.87  tff(c_496, plain, (![A_317, B_318]: (k7_relat_1(A_317, B_318)=k1_xboole_0 | ~r1_xboole_0(B_318, k1_relat_1(A_317)) | ~v1_relat_1(A_317))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.57/2.87  tff(c_507, plain, (![A_319]: (k7_relat_1(A_319, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_319))), inference(resolution, [status(thm)], [c_394, c_496])).
% 7.57/2.87  tff(c_514, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_507])).
% 7.57/2.87  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_237])).
% 7.57/2.87  tff(c_94, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_87])).
% 7.57/2.87  tff(c_515, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_94, c_507])).
% 7.57/2.87  tff(c_74, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 7.57/2.87  tff(c_70, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_237])).
% 7.57/2.87  tff(c_66, plain, (r1_subset_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_237])).
% 7.57/2.87  tff(c_3420, plain, (![A_792, B_793]: (r1_xboole_0(A_792, B_793) | ~r1_subset_1(A_792, B_793) | v1_xboole_0(B_793) | v1_xboole_0(A_792))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.57/2.87  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.57/2.87  tff(c_4153, plain, (![A_883, B_884]: (k3_xboole_0(A_883, B_884)=k1_xboole_0 | ~r1_subset_1(A_883, B_884) | v1_xboole_0(B_884) | v1_xboole_0(A_883))), inference(resolution, [status(thm)], [c_3420, c_2])).
% 7.57/2.87  tff(c_4156, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_4153])).
% 7.57/2.87  tff(c_4159, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_70, c_4156])).
% 7.57/2.87  tff(c_3448, plain, (![A_797, B_798, C_799]: (k9_subset_1(A_797, B_798, C_799)=k3_xboole_0(B_798, C_799) | ~m1_subset_1(C_799, k1_zfmisc_1(A_797)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.57/2.87  tff(c_3459, plain, (![B_798]: (k9_subset_1('#skF_2', B_798, '#skF_5')=k3_xboole_0(B_798, '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_3448])).
% 7.57/2.87  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_237])).
% 7.57/2.87  tff(c_62, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 7.57/2.87  tff(c_76, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 7.57/2.87  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_237])).
% 7.57/2.87  tff(c_56, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 7.57/2.87  tff(c_4353, plain, (![F_907, D_908, B_906, A_909, E_910, C_911]: (v1_funct_1(k1_tmap_1(A_909, B_906, C_911, D_908, E_910, F_907)) | ~m1_subset_1(F_907, k1_zfmisc_1(k2_zfmisc_1(D_908, B_906))) | ~v1_funct_2(F_907, D_908, B_906) | ~v1_funct_1(F_907) | ~m1_subset_1(E_910, k1_zfmisc_1(k2_zfmisc_1(C_911, B_906))) | ~v1_funct_2(E_910, C_911, B_906) | ~v1_funct_1(E_910) | ~m1_subset_1(D_908, k1_zfmisc_1(A_909)) | v1_xboole_0(D_908) | ~m1_subset_1(C_911, k1_zfmisc_1(A_909)) | v1_xboole_0(C_911) | v1_xboole_0(B_906) | v1_xboole_0(A_909))), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.57/2.87  tff(c_4355, plain, (![A_909, C_911, E_910]: (v1_funct_1(k1_tmap_1(A_909, '#skF_3', C_911, '#skF_5', E_910, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_910, k1_zfmisc_1(k2_zfmisc_1(C_911, '#skF_3'))) | ~v1_funct_2(E_910, C_911, '#skF_3') | ~v1_funct_1(E_910) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_909)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_911, k1_zfmisc_1(A_909)) | v1_xboole_0(C_911) | v1_xboole_0('#skF_3') | v1_xboole_0(A_909))), inference(resolution, [status(thm)], [c_54, c_4353])).
% 7.57/2.87  tff(c_4360, plain, (![A_909, C_911, E_910]: (v1_funct_1(k1_tmap_1(A_909, '#skF_3', C_911, '#skF_5', E_910, '#skF_7')) | ~m1_subset_1(E_910, k1_zfmisc_1(k2_zfmisc_1(C_911, '#skF_3'))) | ~v1_funct_2(E_910, C_911, '#skF_3') | ~v1_funct_1(E_910) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_909)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_911, k1_zfmisc_1(A_909)) | v1_xboole_0(C_911) | v1_xboole_0('#skF_3') | v1_xboole_0(A_909))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_4355])).
% 7.57/2.87  tff(c_4403, plain, (![A_919, C_920, E_921]: (v1_funct_1(k1_tmap_1(A_919, '#skF_3', C_920, '#skF_5', E_921, '#skF_7')) | ~m1_subset_1(E_921, k1_zfmisc_1(k2_zfmisc_1(C_920, '#skF_3'))) | ~v1_funct_2(E_921, C_920, '#skF_3') | ~v1_funct_1(E_921) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_919)) | ~m1_subset_1(C_920, k1_zfmisc_1(A_919)) | v1_xboole_0(C_920) | v1_xboole_0(A_919))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_4360])).
% 7.57/2.87  tff(c_4407, plain, (![A_919]: (v1_funct_1(k1_tmap_1(A_919, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_919)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_919)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_919))), inference(resolution, [status(thm)], [c_60, c_4403])).
% 7.57/2.87  tff(c_4414, plain, (![A_919]: (v1_funct_1(k1_tmap_1(A_919, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_919)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_919)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_919))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_4407])).
% 7.57/2.87  tff(c_4490, plain, (![A_945]: (v1_funct_1(k1_tmap_1(A_945, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_945)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_945)) | v1_xboole_0(A_945))), inference(negUnitSimplification, [status(thm)], [c_74, c_4414])).
% 7.57/2.87  tff(c_4493, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_4490])).
% 7.57/2.87  tff(c_4496, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4493])).
% 7.57/2.87  tff(c_4497, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_4496])).
% 7.57/2.87  tff(c_4088, plain, (![A_874, B_875, C_876, D_877]: (k2_partfun1(A_874, B_875, C_876, D_877)=k7_relat_1(C_876, D_877) | ~m1_subset_1(C_876, k1_zfmisc_1(k2_zfmisc_1(A_874, B_875))) | ~v1_funct_1(C_876))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.57/2.87  tff(c_4092, plain, (![D_877]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_877)=k7_relat_1('#skF_6', D_877) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_60, c_4088])).
% 7.57/2.87  tff(c_4098, plain, (![D_877]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_877)=k7_relat_1('#skF_6', D_877))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4092])).
% 7.57/2.87  tff(c_4090, plain, (![D_877]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_877)=k7_relat_1('#skF_7', D_877) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_54, c_4088])).
% 7.57/2.87  tff(c_4095, plain, (![D_877]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_877)=k7_relat_1('#skF_7', D_877))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4090])).
% 7.57/2.87  tff(c_48, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (v1_funct_2(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k4_subset_1(A_162, C_164, D_165), B_163) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.57/2.87  tff(c_46, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (m1_subset_1(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_162, C_164, D_165), B_163))) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.57/2.87  tff(c_4728, plain, (![F_972, A_973, B_975, E_974, D_976, C_977]: (k2_partfun1(k4_subset_1(A_973, C_977, D_976), B_975, k1_tmap_1(A_973, B_975, C_977, D_976, E_974, F_972), C_977)=E_974 | ~m1_subset_1(k1_tmap_1(A_973, B_975, C_977, D_976, E_974, F_972), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_973, C_977, D_976), B_975))) | ~v1_funct_2(k1_tmap_1(A_973, B_975, C_977, D_976, E_974, F_972), k4_subset_1(A_973, C_977, D_976), B_975) | ~v1_funct_1(k1_tmap_1(A_973, B_975, C_977, D_976, E_974, F_972)) | k2_partfun1(D_976, B_975, F_972, k9_subset_1(A_973, C_977, D_976))!=k2_partfun1(C_977, B_975, E_974, k9_subset_1(A_973, C_977, D_976)) | ~m1_subset_1(F_972, k1_zfmisc_1(k2_zfmisc_1(D_976, B_975))) | ~v1_funct_2(F_972, D_976, B_975) | ~v1_funct_1(F_972) | ~m1_subset_1(E_974, k1_zfmisc_1(k2_zfmisc_1(C_977, B_975))) | ~v1_funct_2(E_974, C_977, B_975) | ~v1_funct_1(E_974) | ~m1_subset_1(D_976, k1_zfmisc_1(A_973)) | v1_xboole_0(D_976) | ~m1_subset_1(C_977, k1_zfmisc_1(A_973)) | v1_xboole_0(C_977) | v1_xboole_0(B_975) | v1_xboole_0(A_973))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.57/2.87  tff(c_5429, plain, (![D_1115, F_1114, B_1113, A_1116, C_1118, E_1117]: (k2_partfun1(k4_subset_1(A_1116, C_1118, D_1115), B_1113, k1_tmap_1(A_1116, B_1113, C_1118, D_1115, E_1117, F_1114), C_1118)=E_1117 | ~v1_funct_2(k1_tmap_1(A_1116, B_1113, C_1118, D_1115, E_1117, F_1114), k4_subset_1(A_1116, C_1118, D_1115), B_1113) | ~v1_funct_1(k1_tmap_1(A_1116, B_1113, C_1118, D_1115, E_1117, F_1114)) | k2_partfun1(D_1115, B_1113, F_1114, k9_subset_1(A_1116, C_1118, D_1115))!=k2_partfun1(C_1118, B_1113, E_1117, k9_subset_1(A_1116, C_1118, D_1115)) | ~m1_subset_1(F_1114, k1_zfmisc_1(k2_zfmisc_1(D_1115, B_1113))) | ~v1_funct_2(F_1114, D_1115, B_1113) | ~v1_funct_1(F_1114) | ~m1_subset_1(E_1117, k1_zfmisc_1(k2_zfmisc_1(C_1118, B_1113))) | ~v1_funct_2(E_1117, C_1118, B_1113) | ~v1_funct_1(E_1117) | ~m1_subset_1(D_1115, k1_zfmisc_1(A_1116)) | v1_xboole_0(D_1115) | ~m1_subset_1(C_1118, k1_zfmisc_1(A_1116)) | v1_xboole_0(C_1118) | v1_xboole_0(B_1113) | v1_xboole_0(A_1116))), inference(resolution, [status(thm)], [c_46, c_4728])).
% 7.57/2.87  tff(c_5683, plain, (![F_1157, B_1156, D_1158, A_1159, C_1161, E_1160]: (k2_partfun1(k4_subset_1(A_1159, C_1161, D_1158), B_1156, k1_tmap_1(A_1159, B_1156, C_1161, D_1158, E_1160, F_1157), C_1161)=E_1160 | ~v1_funct_1(k1_tmap_1(A_1159, B_1156, C_1161, D_1158, E_1160, F_1157)) | k2_partfun1(D_1158, B_1156, F_1157, k9_subset_1(A_1159, C_1161, D_1158))!=k2_partfun1(C_1161, B_1156, E_1160, k9_subset_1(A_1159, C_1161, D_1158)) | ~m1_subset_1(F_1157, k1_zfmisc_1(k2_zfmisc_1(D_1158, B_1156))) | ~v1_funct_2(F_1157, D_1158, B_1156) | ~v1_funct_1(F_1157) | ~m1_subset_1(E_1160, k1_zfmisc_1(k2_zfmisc_1(C_1161, B_1156))) | ~v1_funct_2(E_1160, C_1161, B_1156) | ~v1_funct_1(E_1160) | ~m1_subset_1(D_1158, k1_zfmisc_1(A_1159)) | v1_xboole_0(D_1158) | ~m1_subset_1(C_1161, k1_zfmisc_1(A_1159)) | v1_xboole_0(C_1161) | v1_xboole_0(B_1156) | v1_xboole_0(A_1159))), inference(resolution, [status(thm)], [c_48, c_5429])).
% 7.57/2.87  tff(c_5687, plain, (![A_1159, C_1161, E_1160]: (k2_partfun1(k4_subset_1(A_1159, C_1161, '#skF_5'), '#skF_3', k1_tmap_1(A_1159, '#skF_3', C_1161, '#skF_5', E_1160, '#skF_7'), C_1161)=E_1160 | ~v1_funct_1(k1_tmap_1(A_1159, '#skF_3', C_1161, '#skF_5', E_1160, '#skF_7')) | k2_partfun1(C_1161, '#skF_3', E_1160, k9_subset_1(A_1159, C_1161, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_1159, C_1161, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1160, k1_zfmisc_1(k2_zfmisc_1(C_1161, '#skF_3'))) | ~v1_funct_2(E_1160, C_1161, '#skF_3') | ~v1_funct_1(E_1160) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1159)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1161, k1_zfmisc_1(A_1159)) | v1_xboole_0(C_1161) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1159))), inference(resolution, [status(thm)], [c_54, c_5683])).
% 7.57/2.87  tff(c_5693, plain, (![A_1159, C_1161, E_1160]: (k2_partfun1(k4_subset_1(A_1159, C_1161, '#skF_5'), '#skF_3', k1_tmap_1(A_1159, '#skF_3', C_1161, '#skF_5', E_1160, '#skF_7'), C_1161)=E_1160 | ~v1_funct_1(k1_tmap_1(A_1159, '#skF_3', C_1161, '#skF_5', E_1160, '#skF_7')) | k2_partfun1(C_1161, '#skF_3', E_1160, k9_subset_1(A_1159, C_1161, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1159, C_1161, '#skF_5')) | ~m1_subset_1(E_1160, k1_zfmisc_1(k2_zfmisc_1(C_1161, '#skF_3'))) | ~v1_funct_2(E_1160, C_1161, '#skF_3') | ~v1_funct_1(E_1160) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1159)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1161, k1_zfmisc_1(A_1159)) | v1_xboole_0(C_1161) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1159))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_4095, c_5687])).
% 7.57/2.87  tff(c_5999, plain, (![A_1218, C_1219, E_1220]: (k2_partfun1(k4_subset_1(A_1218, C_1219, '#skF_5'), '#skF_3', k1_tmap_1(A_1218, '#skF_3', C_1219, '#skF_5', E_1220, '#skF_7'), C_1219)=E_1220 | ~v1_funct_1(k1_tmap_1(A_1218, '#skF_3', C_1219, '#skF_5', E_1220, '#skF_7')) | k2_partfun1(C_1219, '#skF_3', E_1220, k9_subset_1(A_1218, C_1219, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1218, C_1219, '#skF_5')) | ~m1_subset_1(E_1220, k1_zfmisc_1(k2_zfmisc_1(C_1219, '#skF_3'))) | ~v1_funct_2(E_1220, C_1219, '#skF_3') | ~v1_funct_1(E_1220) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1218)) | ~m1_subset_1(C_1219, k1_zfmisc_1(A_1218)) | v1_xboole_0(C_1219) | v1_xboole_0(A_1218))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_5693])).
% 7.57/2.87  tff(c_6006, plain, (![A_1218]: (k2_partfun1(k4_subset_1(A_1218, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1218, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1218, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_1218, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1218, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1218)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1218)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1218))), inference(resolution, [status(thm)], [c_60, c_5999])).
% 7.57/2.87  tff(c_6016, plain, (![A_1218]: (k2_partfun1(k4_subset_1(A_1218, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1218, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1218, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1218, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1218, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1218)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1218)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1218))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_4098, c_6006])).
% 7.57/2.87  tff(c_6078, plain, (![A_1226]: (k2_partfun1(k4_subset_1(A_1226, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1226, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1226, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1226, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1226, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1226)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1226)) | v1_xboole_0(A_1226))), inference(negUnitSimplification, [status(thm)], [c_74, c_6016])).
% 7.57/2.87  tff(c_541, plain, (![A_323, B_324]: (r1_xboole_0(A_323, B_324) | ~r1_subset_1(A_323, B_324) | v1_xboole_0(B_324) | v1_xboole_0(A_323))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.57/2.87  tff(c_1480, plain, (![A_443, B_444]: (k3_xboole_0(A_443, B_444)=k1_xboole_0 | ~r1_subset_1(A_443, B_444) | v1_xboole_0(B_444) | v1_xboole_0(A_443))), inference(resolution, [status(thm)], [c_541, c_2])).
% 7.57/2.87  tff(c_1483, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_1480])).
% 7.57/2.87  tff(c_1486, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_70, c_1483])).
% 7.57/2.87  tff(c_565, plain, (![A_328, B_329, C_330]: (k9_subset_1(A_328, B_329, C_330)=k3_xboole_0(B_329, C_330) | ~m1_subset_1(C_330, k1_zfmisc_1(A_328)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.57/2.87  tff(c_576, plain, (![B_329]: (k9_subset_1('#skF_2', B_329, '#skF_5')=k3_xboole_0(B_329, '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_565])).
% 7.57/2.87  tff(c_1762, plain, (![B_481, F_482, C_486, E_485, D_483, A_484]: (v1_funct_1(k1_tmap_1(A_484, B_481, C_486, D_483, E_485, F_482)) | ~m1_subset_1(F_482, k1_zfmisc_1(k2_zfmisc_1(D_483, B_481))) | ~v1_funct_2(F_482, D_483, B_481) | ~v1_funct_1(F_482) | ~m1_subset_1(E_485, k1_zfmisc_1(k2_zfmisc_1(C_486, B_481))) | ~v1_funct_2(E_485, C_486, B_481) | ~v1_funct_1(E_485) | ~m1_subset_1(D_483, k1_zfmisc_1(A_484)) | v1_xboole_0(D_483) | ~m1_subset_1(C_486, k1_zfmisc_1(A_484)) | v1_xboole_0(C_486) | v1_xboole_0(B_481) | v1_xboole_0(A_484))), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.57/2.87  tff(c_1764, plain, (![A_484, C_486, E_485]: (v1_funct_1(k1_tmap_1(A_484, '#skF_3', C_486, '#skF_5', E_485, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_485, k1_zfmisc_1(k2_zfmisc_1(C_486, '#skF_3'))) | ~v1_funct_2(E_485, C_486, '#skF_3') | ~v1_funct_1(E_485) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_484)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_486, k1_zfmisc_1(A_484)) | v1_xboole_0(C_486) | v1_xboole_0('#skF_3') | v1_xboole_0(A_484))), inference(resolution, [status(thm)], [c_54, c_1762])).
% 7.57/2.87  tff(c_1769, plain, (![A_484, C_486, E_485]: (v1_funct_1(k1_tmap_1(A_484, '#skF_3', C_486, '#skF_5', E_485, '#skF_7')) | ~m1_subset_1(E_485, k1_zfmisc_1(k2_zfmisc_1(C_486, '#skF_3'))) | ~v1_funct_2(E_485, C_486, '#skF_3') | ~v1_funct_1(E_485) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_484)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_486, k1_zfmisc_1(A_484)) | v1_xboole_0(C_486) | v1_xboole_0('#skF_3') | v1_xboole_0(A_484))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1764])).
% 7.57/2.87  tff(c_2119, plain, (![A_550, C_551, E_552]: (v1_funct_1(k1_tmap_1(A_550, '#skF_3', C_551, '#skF_5', E_552, '#skF_7')) | ~m1_subset_1(E_552, k1_zfmisc_1(k2_zfmisc_1(C_551, '#skF_3'))) | ~v1_funct_2(E_552, C_551, '#skF_3') | ~v1_funct_1(E_552) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_550)) | ~m1_subset_1(C_551, k1_zfmisc_1(A_550)) | v1_xboole_0(C_551) | v1_xboole_0(A_550))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_1769])).
% 7.57/2.87  tff(c_2126, plain, (![A_550]: (v1_funct_1(k1_tmap_1(A_550, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_550)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_550)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_550))), inference(resolution, [status(thm)], [c_60, c_2119])).
% 7.57/2.87  tff(c_2136, plain, (![A_550]: (v1_funct_1(k1_tmap_1(A_550, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_550)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_550)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_550))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2126])).
% 7.57/2.87  tff(c_2145, plain, (![A_554]: (v1_funct_1(k1_tmap_1(A_554, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_554)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_554)) | v1_xboole_0(A_554))), inference(negUnitSimplification, [status(thm)], [c_74, c_2136])).
% 7.57/2.87  tff(c_2148, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_2145])).
% 7.57/2.87  tff(c_2151, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2148])).
% 7.57/2.87  tff(c_2152, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_2151])).
% 7.57/2.87  tff(c_1571, plain, (![A_456, B_457, C_458, D_459]: (k2_partfun1(A_456, B_457, C_458, D_459)=k7_relat_1(C_458, D_459) | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(A_456, B_457))) | ~v1_funct_1(C_458))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.57/2.87  tff(c_1575, plain, (![D_459]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_459)=k7_relat_1('#skF_6', D_459) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_60, c_1571])).
% 7.57/2.87  tff(c_1581, plain, (![D_459]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_459)=k7_relat_1('#skF_6', D_459))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1575])).
% 7.57/2.87  tff(c_1573, plain, (![D_459]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_459)=k7_relat_1('#skF_7', D_459) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_54, c_1571])).
% 7.57/2.87  tff(c_1578, plain, (![D_459]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_459)=k7_relat_1('#skF_7', D_459))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1573])).
% 7.57/2.87  tff(c_2195, plain, (![B_568, F_565, A_566, D_569, E_567, C_570]: (k2_partfun1(k4_subset_1(A_566, C_570, D_569), B_568, k1_tmap_1(A_566, B_568, C_570, D_569, E_567, F_565), D_569)=F_565 | ~m1_subset_1(k1_tmap_1(A_566, B_568, C_570, D_569, E_567, F_565), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_566, C_570, D_569), B_568))) | ~v1_funct_2(k1_tmap_1(A_566, B_568, C_570, D_569, E_567, F_565), k4_subset_1(A_566, C_570, D_569), B_568) | ~v1_funct_1(k1_tmap_1(A_566, B_568, C_570, D_569, E_567, F_565)) | k2_partfun1(D_569, B_568, F_565, k9_subset_1(A_566, C_570, D_569))!=k2_partfun1(C_570, B_568, E_567, k9_subset_1(A_566, C_570, D_569)) | ~m1_subset_1(F_565, k1_zfmisc_1(k2_zfmisc_1(D_569, B_568))) | ~v1_funct_2(F_565, D_569, B_568) | ~v1_funct_1(F_565) | ~m1_subset_1(E_567, k1_zfmisc_1(k2_zfmisc_1(C_570, B_568))) | ~v1_funct_2(E_567, C_570, B_568) | ~v1_funct_1(E_567) | ~m1_subset_1(D_569, k1_zfmisc_1(A_566)) | v1_xboole_0(D_569) | ~m1_subset_1(C_570, k1_zfmisc_1(A_566)) | v1_xboole_0(C_570) | v1_xboole_0(B_568) | v1_xboole_0(A_566))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.57/2.87  tff(c_2820, plain, (![F_695, E_698, C_699, A_697, D_696, B_694]: (k2_partfun1(k4_subset_1(A_697, C_699, D_696), B_694, k1_tmap_1(A_697, B_694, C_699, D_696, E_698, F_695), D_696)=F_695 | ~v1_funct_2(k1_tmap_1(A_697, B_694, C_699, D_696, E_698, F_695), k4_subset_1(A_697, C_699, D_696), B_694) | ~v1_funct_1(k1_tmap_1(A_697, B_694, C_699, D_696, E_698, F_695)) | k2_partfun1(D_696, B_694, F_695, k9_subset_1(A_697, C_699, D_696))!=k2_partfun1(C_699, B_694, E_698, k9_subset_1(A_697, C_699, D_696)) | ~m1_subset_1(F_695, k1_zfmisc_1(k2_zfmisc_1(D_696, B_694))) | ~v1_funct_2(F_695, D_696, B_694) | ~v1_funct_1(F_695) | ~m1_subset_1(E_698, k1_zfmisc_1(k2_zfmisc_1(C_699, B_694))) | ~v1_funct_2(E_698, C_699, B_694) | ~v1_funct_1(E_698) | ~m1_subset_1(D_696, k1_zfmisc_1(A_697)) | v1_xboole_0(D_696) | ~m1_subset_1(C_699, k1_zfmisc_1(A_697)) | v1_xboole_0(C_699) | v1_xboole_0(B_694) | v1_xboole_0(A_697))), inference(resolution, [status(thm)], [c_46, c_2195])).
% 7.57/2.87  tff(c_3023, plain, (![B_736, A_739, C_741, E_740, D_738, F_737]: (k2_partfun1(k4_subset_1(A_739, C_741, D_738), B_736, k1_tmap_1(A_739, B_736, C_741, D_738, E_740, F_737), D_738)=F_737 | ~v1_funct_1(k1_tmap_1(A_739, B_736, C_741, D_738, E_740, F_737)) | k2_partfun1(D_738, B_736, F_737, k9_subset_1(A_739, C_741, D_738))!=k2_partfun1(C_741, B_736, E_740, k9_subset_1(A_739, C_741, D_738)) | ~m1_subset_1(F_737, k1_zfmisc_1(k2_zfmisc_1(D_738, B_736))) | ~v1_funct_2(F_737, D_738, B_736) | ~v1_funct_1(F_737) | ~m1_subset_1(E_740, k1_zfmisc_1(k2_zfmisc_1(C_741, B_736))) | ~v1_funct_2(E_740, C_741, B_736) | ~v1_funct_1(E_740) | ~m1_subset_1(D_738, k1_zfmisc_1(A_739)) | v1_xboole_0(D_738) | ~m1_subset_1(C_741, k1_zfmisc_1(A_739)) | v1_xboole_0(C_741) | v1_xboole_0(B_736) | v1_xboole_0(A_739))), inference(resolution, [status(thm)], [c_48, c_2820])).
% 7.57/2.87  tff(c_3027, plain, (![A_739, C_741, E_740]: (k2_partfun1(k4_subset_1(A_739, C_741, '#skF_5'), '#skF_3', k1_tmap_1(A_739, '#skF_3', C_741, '#skF_5', E_740, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_739, '#skF_3', C_741, '#skF_5', E_740, '#skF_7')) | k2_partfun1(C_741, '#skF_3', E_740, k9_subset_1(A_739, C_741, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_739, C_741, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_740, k1_zfmisc_1(k2_zfmisc_1(C_741, '#skF_3'))) | ~v1_funct_2(E_740, C_741, '#skF_3') | ~v1_funct_1(E_740) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_739)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_741, k1_zfmisc_1(A_739)) | v1_xboole_0(C_741) | v1_xboole_0('#skF_3') | v1_xboole_0(A_739))), inference(resolution, [status(thm)], [c_54, c_3023])).
% 7.57/2.87  tff(c_3033, plain, (![A_739, C_741, E_740]: (k2_partfun1(k4_subset_1(A_739, C_741, '#skF_5'), '#skF_3', k1_tmap_1(A_739, '#skF_3', C_741, '#skF_5', E_740, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_739, '#skF_3', C_741, '#skF_5', E_740, '#skF_7')) | k2_partfun1(C_741, '#skF_3', E_740, k9_subset_1(A_739, C_741, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_739, C_741, '#skF_5')) | ~m1_subset_1(E_740, k1_zfmisc_1(k2_zfmisc_1(C_741, '#skF_3'))) | ~v1_funct_2(E_740, C_741, '#skF_3') | ~v1_funct_1(E_740) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_739)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_741, k1_zfmisc_1(A_739)) | v1_xboole_0(C_741) | v1_xboole_0('#skF_3') | v1_xboole_0(A_739))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1578, c_3027])).
% 7.57/2.87  tff(c_3318, plain, (![A_784, C_785, E_786]: (k2_partfun1(k4_subset_1(A_784, C_785, '#skF_5'), '#skF_3', k1_tmap_1(A_784, '#skF_3', C_785, '#skF_5', E_786, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_784, '#skF_3', C_785, '#skF_5', E_786, '#skF_7')) | k2_partfun1(C_785, '#skF_3', E_786, k9_subset_1(A_784, C_785, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_784, C_785, '#skF_5')) | ~m1_subset_1(E_786, k1_zfmisc_1(k2_zfmisc_1(C_785, '#skF_3'))) | ~v1_funct_2(E_786, C_785, '#skF_3') | ~v1_funct_1(E_786) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_784)) | ~m1_subset_1(C_785, k1_zfmisc_1(A_784)) | v1_xboole_0(C_785) | v1_xboole_0(A_784))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_3033])).
% 7.57/2.87  tff(c_3325, plain, (![A_784]: (k2_partfun1(k4_subset_1(A_784, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_784, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_784, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_784, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_784, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_784)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_784)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_784))), inference(resolution, [status(thm)], [c_60, c_3318])).
% 7.57/2.87  tff(c_3335, plain, (![A_784]: (k2_partfun1(k4_subset_1(A_784, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_784, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_784, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_784, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_784, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_784)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_784)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_784))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1581, c_3325])).
% 7.57/2.87  tff(c_3390, plain, (![A_791]: (k2_partfun1(k4_subset_1(A_791, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_791, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_791, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_791, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_791, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_791)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_791)) | v1_xboole_0(A_791))), inference(negUnitSimplification, [status(thm)], [c_74, c_3335])).
% 7.57/2.87  tff(c_102, plain, (![A_237, B_238]: (r2_hidden('#skF_1'(A_237, B_238), A_237) | r1_xboole_0(A_237, B_238))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.57/2.87  tff(c_142, plain, (![A_248, B_249]: (~r1_tarski(A_248, '#skF_1'(A_248, B_249)) | r1_xboole_0(A_248, B_249))), inference(resolution, [status(thm)], [c_102, c_22])).
% 7.57/2.87  tff(c_147, plain, (![B_249]: (r1_xboole_0(k1_xboole_0, B_249))), inference(resolution, [status(thm)], [c_12, c_142])).
% 7.57/2.87  tff(c_190, plain, (![A_258, B_259]: (k7_relat_1(A_258, B_259)=k1_xboole_0 | ~r1_xboole_0(B_259, k1_relat_1(A_258)) | ~v1_relat_1(A_258))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.57/2.87  tff(c_201, plain, (![A_260]: (k7_relat_1(A_260, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_260))), inference(resolution, [status(thm)], [c_147, c_190])).
% 7.57/2.87  tff(c_208, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_201])).
% 7.57/2.87  tff(c_346, plain, (![A_284, B_285, C_286, D_287]: (k2_partfun1(A_284, B_285, C_286, D_287)=k7_relat_1(C_286, D_287) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))) | ~v1_funct_1(C_286))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.57/2.87  tff(c_350, plain, (![D_287]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_287)=k7_relat_1('#skF_6', D_287) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_60, c_346])).
% 7.57/2.87  tff(c_356, plain, (![D_287]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_287)=k7_relat_1('#skF_6', D_287))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_350])).
% 7.57/2.87  tff(c_209, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_94, c_201])).
% 7.57/2.87  tff(c_348, plain, (![D_287]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_287)=k7_relat_1('#skF_7', D_287) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_54, c_346])).
% 7.57/2.87  tff(c_353, plain, (![D_287]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_287)=k7_relat_1('#skF_7', D_287))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_348])).
% 7.57/2.87  tff(c_218, plain, (![A_261, B_262]: (r1_xboole_0(A_261, B_262) | ~r1_subset_1(A_261, B_262) | v1_xboole_0(B_262) | v1_xboole_0(A_261))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.57/2.87  tff(c_330, plain, (![A_282, B_283]: (k3_xboole_0(A_282, B_283)=k1_xboole_0 | ~r1_subset_1(A_282, B_283) | v1_xboole_0(B_283) | v1_xboole_0(A_282))), inference(resolution, [status(thm)], [c_218, c_2])).
% 7.57/2.87  tff(c_336, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_330])).
% 7.57/2.87  tff(c_340, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_70, c_336])).
% 7.57/2.87  tff(c_251, plain, (![A_266, B_267, C_268]: (k9_subset_1(A_266, B_267, C_268)=k3_xboole_0(B_267, C_268) | ~m1_subset_1(C_268, k1_zfmisc_1(A_266)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.57/2.87  tff(c_262, plain, (![B_267]: (k9_subset_1('#skF_2', B_267, '#skF_5')=k3_xboole_0(B_267, '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_251])).
% 7.57/2.87  tff(c_52, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 7.57/2.87  tff(c_96, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_52])).
% 7.57/2.87  tff(c_264, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_262, c_96])).
% 7.57/2.87  tff(c_341, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k1_xboole_0)!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_340, c_340, c_264])).
% 7.57/2.87  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_208, c_356, c_209, c_353, c_341])).
% 7.57/2.87  tff(c_377, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_52])).
% 7.57/2.87  tff(c_540, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_377])).
% 7.57/2.87  tff(c_3401, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3390, c_540])).
% 7.57/2.87  tff(c_3415, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_514, c_515, c_1486, c_576, c_1486, c_576, c_2152, c_3401])).
% 7.57/2.87  tff(c_3417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_3415])).
% 7.57/2.87  tff(c_3418, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_377])).
% 7.57/2.87  tff(c_6087, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6078, c_3418])).
% 7.57/2.87  tff(c_6098, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_514, c_515, c_4159, c_3459, c_4159, c_3459, c_4497, c_6087])).
% 7.57/2.87  tff(c_6100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_6098])).
% 7.57/2.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.57/2.87  
% 7.57/2.87  Inference rules
% 7.57/2.87  ----------------------
% 7.57/2.87  #Ref     : 0
% 7.57/2.87  #Sup     : 1238
% 7.57/2.87  #Fact    : 0
% 7.57/2.87  #Define  : 0
% 7.57/2.87  #Split   : 42
% 7.57/2.87  #Chain   : 0
% 7.57/2.87  #Close   : 0
% 7.57/2.87  
% 7.57/2.87  Ordering : KBO
% 7.57/2.87  
% 7.57/2.87  Simplification rules
% 7.57/2.87  ----------------------
% 7.57/2.87  #Subsume      : 147
% 7.57/2.87  #Demod        : 873
% 7.57/2.87  #Tautology    : 586
% 7.57/2.87  #SimpNegUnit  : 255
% 7.57/2.87  #BackRed      : 14
% 7.57/2.87  
% 7.57/2.87  #Partial instantiations: 0
% 7.57/2.87  #Strategies tried      : 1
% 7.57/2.87  
% 7.57/2.87  Timing (in seconds)
% 7.57/2.87  ----------------------
% 7.57/2.88  Preprocessing        : 0.44
% 7.57/2.88  Parsing              : 0.22
% 7.57/2.88  CNF conversion       : 0.06
% 7.57/2.88  Main loop            : 1.56
% 7.57/2.88  Inferencing          : 0.58
% 7.57/2.88  Reduction            : 0.51
% 7.57/2.88  Demodulation         : 0.37
% 7.57/2.88  BG Simplification    : 0.06
% 7.57/2.88  Subsumption          : 0.31
% 7.57/2.88  Abstraction          : 0.08
% 7.57/2.88  MUC search           : 0.00
% 7.57/2.88  Cooper               : 0.00
% 7.57/2.88  Total                : 2.06
% 7.57/2.88  Index Insertion      : 0.00
% 7.57/2.88  Index Deletion       : 0.00
% 7.57/2.88  Index Matching       : 0.00
% 7.57/2.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
