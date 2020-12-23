%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:19 EST 2020

% Result     : Theorem 6.96s
% Output     : CNFRefutation 7.27s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 999 expanded)
%              Number of leaves         :   38 ( 355 expanded)
%              Depth                    :   20
%              Number of atoms          :  684 (6597 expanded)
%              Number of equality atoms :   82 ( 502 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_213,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,u1_struct_0(D),u1_struct_0(B))
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                               => ( ( D = A
                                    & r1_funct_2(u1_struct_0(A),u1_struct_0(B),u1_struct_0(D),u1_struct_0(B),E,G) )
                                 => ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,G),F)
                                  <=> r2_funct_2(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,E,C),F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(c_34,plain,(
    '#skF_5' = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_86,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_124,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_86,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,
    ( k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = '#skF_8'
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_124,c_2])).

tff(c_2709,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_1241,plain,(
    ! [C_424,B_425,A_426] :
      ( v1_xboole_0(C_424)
      | ~ m1_subset_1(C_424,k1_zfmisc_1(k2_zfmisc_1(B_425,A_426)))
      | ~ v1_xboole_0(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1255,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_86,c_1241])).

tff(c_1266,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1255])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_50,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_40,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_38,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_85,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_32,plain,(
    r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_87,plain,(
    r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32])).

tff(c_2290,plain,(
    ! [C_594,E_595,F_598,B_596,A_597,D_599] :
      ( F_598 = E_595
      | ~ r1_funct_2(A_597,B_596,C_594,D_599,E_595,F_598)
      | ~ m1_subset_1(F_598,k1_zfmisc_1(k2_zfmisc_1(C_594,D_599)))
      | ~ v1_funct_2(F_598,C_594,D_599)
      | ~ v1_funct_1(F_598)
      | ~ m1_subset_1(E_595,k1_zfmisc_1(k2_zfmisc_1(A_597,B_596)))
      | ~ v1_funct_2(E_595,A_597,B_596)
      | ~ v1_funct_1(E_595)
      | v1_xboole_0(D_599)
      | v1_xboole_0(B_596) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2292,plain,
    ( '#skF_6' = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_87,c_2290])).

tff(c_2295,plain,
    ( '#skF_6' = '#skF_8'
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_40,c_85,c_86,c_2292])).

tff(c_2296,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1266,c_2295])).

tff(c_1809,plain,(
    ! [C_513,D_518,B_515,A_516,F_517,E_514] :
      ( F_517 = E_514
      | ~ r1_funct_2(A_516,B_515,C_513,D_518,E_514,F_517)
      | ~ m1_subset_1(F_517,k1_zfmisc_1(k2_zfmisc_1(C_513,D_518)))
      | ~ v1_funct_2(F_517,C_513,D_518)
      | ~ v1_funct_1(F_517)
      | ~ m1_subset_1(E_514,k1_zfmisc_1(k2_zfmisc_1(A_516,B_515)))
      | ~ v1_funct_2(E_514,A_516,B_515)
      | ~ v1_funct_1(E_514)
      | v1_xboole_0(D_518)
      | v1_xboole_0(B_515) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1811,plain,
    ( '#skF_6' = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_87,c_1809])).

tff(c_1814,plain,
    ( '#skF_6' = '#skF_8'
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_40,c_85,c_86,c_1811])).

tff(c_1815,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1266,c_1814])).

tff(c_80,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_8'),'#skF_7')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_82,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_80])).

tff(c_1608,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_1818,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1815,c_1608])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_83,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_54])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_2039,plain,(
    ! [C_555,B_553,D_556,E_557,A_554] :
      ( k3_tmap_1(A_554,B_553,C_555,D_556,E_557) = k2_partfun1(u1_struct_0(C_555),u1_struct_0(B_553),E_557,u1_struct_0(D_556))
      | ~ m1_pre_topc(D_556,C_555)
      | ~ m1_subset_1(E_557,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_555),u1_struct_0(B_553))))
      | ~ v1_funct_2(E_557,u1_struct_0(C_555),u1_struct_0(B_553))
      | ~ v1_funct_1(E_557)
      | ~ m1_pre_topc(D_556,A_554)
      | ~ m1_pre_topc(C_555,A_554)
      | ~ l1_pre_topc(B_553)
      | ~ v2_pre_topc(B_553)
      | v2_struct_0(B_553)
      | ~ l1_pre_topc(A_554)
      | ~ v2_pre_topc(A_554)
      | v2_struct_0(A_554) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2046,plain,(
    ! [A_554,D_556] :
      ( k3_tmap_1(A_554,'#skF_3','#skF_2',D_556,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_556))
      | ~ m1_pre_topc(D_556,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc(D_556,A_554)
      | ~ m1_pre_topc('#skF_2',A_554)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_554)
      | ~ v2_pre_topc(A_554)
      | v2_struct_0(A_554) ) ),
    inference(resolution,[status(thm)],[c_86,c_2039])).

tff(c_2056,plain,(
    ! [A_554,D_556] :
      ( k3_tmap_1(A_554,'#skF_3','#skF_2',D_556,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_556))
      | ~ m1_pre_topc(D_556,'#skF_2')
      | ~ m1_pre_topc(D_556,A_554)
      | ~ m1_pre_topc('#skF_2',A_554)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_554)
      | ~ v2_pre_topc(A_554)
      | v2_struct_0(A_554) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_40,c_85,c_2046])).

tff(c_2077,plain,(
    ! [A_562,D_563] :
      ( k3_tmap_1(A_562,'#skF_3','#skF_2',D_563,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_563))
      | ~ m1_pre_topc(D_563,'#skF_2')
      | ~ m1_pre_topc(D_563,A_562)
      | ~ m1_pre_topc('#skF_2',A_562)
      | ~ l1_pre_topc(A_562)
      | ~ v2_pre_topc(A_562)
      | v2_struct_0(A_562) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2056])).

tff(c_2079,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_2077])).

tff(c_2084,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_83,c_58,c_2079])).

tff(c_2085,plain,(
    k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2084])).

tff(c_1897,plain,(
    ! [A_530,B_531,C_532,D_533] :
      ( k2_partfun1(u1_struct_0(A_530),u1_struct_0(B_531),C_532,u1_struct_0(D_533)) = k2_tmap_1(A_530,B_531,C_532,D_533)
      | ~ m1_pre_topc(D_533,A_530)
      | ~ m1_subset_1(C_532,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_530),u1_struct_0(B_531))))
      | ~ v1_funct_2(C_532,u1_struct_0(A_530),u1_struct_0(B_531))
      | ~ v1_funct_1(C_532)
      | ~ l1_pre_topc(B_531)
      | ~ v2_pre_topc(B_531)
      | v2_struct_0(B_531)
      | ~ l1_pre_topc(A_530)
      | ~ v2_pre_topc(A_530)
      | v2_struct_0(A_530) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1904,plain,(
    ! [D_533] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_533)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_533)
      | ~ m1_pre_topc(D_533,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_86,c_1897])).

tff(c_1914,plain,(
    ! [D_533] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_533)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_533)
      | ~ m1_pre_topc(D_533,'#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_40,c_85,c_1904])).

tff(c_1915,plain,(
    ! [D_533] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_533)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_533)
      | ~ m1_pre_topc(D_533,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_1914])).

tff(c_2093,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2085,c_1915])).

tff(c_2100,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2093])).

tff(c_74,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7')
    | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_84,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7')
    | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_74])).

tff(c_1658,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1608,c_84])).

tff(c_2105,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2100,c_1658])).

tff(c_2108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1818,c_2105])).

tff(c_2110,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_2299,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2296,c_2110])).

tff(c_2527,plain,(
    ! [A_634,B_633,D_636,C_635,E_637] :
      ( k3_tmap_1(A_634,B_633,C_635,D_636,E_637) = k2_partfun1(u1_struct_0(C_635),u1_struct_0(B_633),E_637,u1_struct_0(D_636))
      | ~ m1_pre_topc(D_636,C_635)
      | ~ m1_subset_1(E_637,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_635),u1_struct_0(B_633))))
      | ~ v1_funct_2(E_637,u1_struct_0(C_635),u1_struct_0(B_633))
      | ~ v1_funct_1(E_637)
      | ~ m1_pre_topc(D_636,A_634)
      | ~ m1_pre_topc(C_635,A_634)
      | ~ l1_pre_topc(B_633)
      | ~ v2_pre_topc(B_633)
      | v2_struct_0(B_633)
      | ~ l1_pre_topc(A_634)
      | ~ v2_pre_topc(A_634)
      | v2_struct_0(A_634) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2534,plain,(
    ! [A_634,D_636] :
      ( k3_tmap_1(A_634,'#skF_3','#skF_2',D_636,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_636))
      | ~ m1_pre_topc(D_636,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc(D_636,A_634)
      | ~ m1_pre_topc('#skF_2',A_634)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_634)
      | ~ v2_pre_topc(A_634)
      | v2_struct_0(A_634) ) ),
    inference(resolution,[status(thm)],[c_86,c_2527])).

tff(c_2544,plain,(
    ! [A_634,D_636] :
      ( k3_tmap_1(A_634,'#skF_3','#skF_2',D_636,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_636))
      | ~ m1_pre_topc(D_636,'#skF_2')
      | ~ m1_pre_topc(D_636,A_634)
      | ~ m1_pre_topc('#skF_2',A_634)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_634)
      | ~ v2_pre_topc(A_634)
      | v2_struct_0(A_634) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_40,c_85,c_2534])).

tff(c_2574,plain,(
    ! [A_644,D_645] :
      ( k3_tmap_1(A_644,'#skF_3','#skF_2',D_645,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_645))
      | ~ m1_pre_topc(D_645,'#skF_2')
      | ~ m1_pre_topc(D_645,A_644)
      | ~ m1_pre_topc('#skF_2',A_644)
      | ~ l1_pre_topc(A_644)
      | ~ v2_pre_topc(A_644)
      | v2_struct_0(A_644) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2544])).

tff(c_2576,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_2574])).

tff(c_2581,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_83,c_58,c_2576])).

tff(c_2582,plain,(
    k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2581])).

tff(c_2388,plain,(
    ! [A_608,B_609,C_610,D_611] :
      ( k2_partfun1(u1_struct_0(A_608),u1_struct_0(B_609),C_610,u1_struct_0(D_611)) = k2_tmap_1(A_608,B_609,C_610,D_611)
      | ~ m1_pre_topc(D_611,A_608)
      | ~ m1_subset_1(C_610,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_608),u1_struct_0(B_609))))
      | ~ v1_funct_2(C_610,u1_struct_0(A_608),u1_struct_0(B_609))
      | ~ v1_funct_1(C_610)
      | ~ l1_pre_topc(B_609)
      | ~ v2_pre_topc(B_609)
      | v2_struct_0(B_609)
      | ~ l1_pre_topc(A_608)
      | ~ v2_pre_topc(A_608)
      | v2_struct_0(A_608) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2395,plain,(
    ! [D_611] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_611)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_611)
      | ~ m1_pre_topc(D_611,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_86,c_2388])).

tff(c_2405,plain,(
    ! [D_611] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_611)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_611)
      | ~ m1_pre_topc(D_611,'#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_40,c_85,c_2395])).

tff(c_2406,plain,(
    ! [D_611] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_611)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_611)
      | ~ m1_pre_topc(D_611,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_2405])).

tff(c_2590,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2582,c_2406])).

tff(c_2597,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2590])).

tff(c_2109,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_2602,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2597,c_2109])).

tff(c_2604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2299,c_2602])).

tff(c_2606,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1255])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2612,plain,(
    ! [A_649,A_650,B_651] :
      ( v1_xboole_0(A_649)
      | ~ v1_xboole_0(A_650)
      | ~ r1_tarski(A_649,k2_zfmisc_1(B_651,A_650)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1241])).

tff(c_2636,plain,(
    ! [B_652,A_653] :
      ( v1_xboole_0(k2_zfmisc_1(B_652,A_653))
      | ~ v1_xboole_0(A_653) ) ),
    inference(resolution,[status(thm)],[c_6,c_2612])).

tff(c_125,plain,(
    ! [C_205,B_206,A_207] :
      ( ~ v1_xboole_0(C_205)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(C_205))
      | ~ r2_hidden(A_207,B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_136,plain,(
    ! [A_207] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_207,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_125])).

tff(c_142,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_2639,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2636,c_142])).

tff(c_2643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2606,c_2639])).

tff(c_2645,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_2712,plain,(
    ! [A_671,B_672,C_673] :
      ( r2_hidden('#skF_1'(A_671,B_672,C_673),B_672)
      | r1_tarski(B_672,C_673)
      | ~ m1_subset_1(C_673,k1_zfmisc_1(A_671))
      | ~ m1_subset_1(B_672,k1_zfmisc_1(A_671)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_137,plain,(
    ! [B_11,A_207,A_10] :
      ( ~ v1_xboole_0(B_11)
      | ~ r2_hidden(A_207,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_125])).

tff(c_2903,plain,(
    ! [B_691,B_692,C_693,A_694] :
      ( ~ v1_xboole_0(B_691)
      | ~ r1_tarski(B_692,B_691)
      | r1_tarski(B_692,C_693)
      | ~ m1_subset_1(C_693,k1_zfmisc_1(A_694))
      | ~ m1_subset_1(B_692,k1_zfmisc_1(A_694)) ) ),
    inference(resolution,[status(thm)],[c_2712,c_137])).

tff(c_2926,plain,(
    ! [B_698,C_699,A_700] :
      ( ~ v1_xboole_0(B_698)
      | r1_tarski(B_698,C_699)
      | ~ m1_subset_1(C_699,k1_zfmisc_1(A_700))
      | ~ m1_subset_1(B_698,k1_zfmisc_1(A_700)) ) ),
    inference(resolution,[status(thm)],[c_6,c_2903])).

tff(c_2940,plain,(
    ! [B_701,A_702,B_703] :
      ( ~ v1_xboole_0(B_701)
      | r1_tarski(B_701,A_702)
      | ~ m1_subset_1(B_701,k1_zfmisc_1(B_703))
      | ~ r1_tarski(A_702,B_703) ) ),
    inference(resolution,[status(thm)],[c_16,c_2926])).

tff(c_2954,plain,(
    ! [A_704,A_705,B_706] :
      ( ~ v1_xboole_0(A_704)
      | r1_tarski(A_704,A_705)
      | ~ r1_tarski(A_705,B_706)
      | ~ r1_tarski(A_704,B_706) ) ),
    inference(resolution,[status(thm)],[c_16,c_2940])).

tff(c_3001,plain,(
    ! [A_713] :
      ( ~ v1_xboole_0(A_713)
      | r1_tarski(A_713,'#skF_8')
      | ~ r1_tarski(A_713,k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_124,c_2954])).

tff(c_3008,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_3001])).

tff(c_3013,plain,(
    r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2645,c_3008])).

tff(c_3015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2709,c_3013])).

tff(c_3016,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_103,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_48,c_14])).

tff(c_108,plain,(
    ! [B_203,A_204] :
      ( B_203 = A_204
      | ~ r1_tarski(B_203,A_204)
      | ~ r1_tarski(A_204,B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,
    ( k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_103,c_108])).

tff(c_2707,plain,(
    ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_3018,plain,(
    ~ r1_tarski('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3016,c_2707])).

tff(c_3021,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3016,c_86])).

tff(c_3023,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3016,c_48])).

tff(c_3059,plain,(
    ! [A_714,B_715,C_716] :
      ( r2_hidden('#skF_1'(A_714,B_715,C_716),B_715)
      | r1_tarski(B_715,C_716)
      | ~ m1_subset_1(C_716,k1_zfmisc_1(A_714))
      | ~ m1_subset_1(B_715,k1_zfmisc_1(A_714)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_134,plain,(
    ! [A_207] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_207,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_86,c_125])).

tff(c_2649,plain,(
    ! [A_207] : ~ r2_hidden(A_207,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2645,c_134])).

tff(c_3080,plain,(
    ! [C_717,A_718] :
      ( r1_tarski('#skF_8',C_717)
      | ~ m1_subset_1(C_717,k1_zfmisc_1(A_718))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_718)) ) ),
    inference(resolution,[status(thm)],[c_3059,c_2649])).

tff(c_3084,plain,
    ( r1_tarski('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_3023,c_3080])).

tff(c_3094,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3021,c_3084])).

tff(c_3096,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3018,c_3094])).

tff(c_3097,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_4088,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3097,c_124])).

tff(c_4108,plain,
    ( '#skF_6' = '#skF_8'
    | ~ r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_4088,c_2])).

tff(c_4129,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4108])).

tff(c_4091,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3097,c_48])).

tff(c_4089,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3097,c_86])).

tff(c_4150,plain,(
    ! [A_896,B_897,C_898] :
      ( r2_hidden('#skF_1'(A_896,B_897,C_898),B_897)
      | r1_tarski(B_897,C_898)
      | ~ m1_subset_1(C_898,k1_zfmisc_1(A_896))
      | ~ m1_subset_1(B_897,k1_zfmisc_1(A_896)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2644,plain,(
    ! [A_207] : ~ r2_hidden(A_207,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_4244,plain,(
    ! [C_911,A_912] :
      ( r1_tarski('#skF_6',C_911)
      | ~ m1_subset_1(C_911,k1_zfmisc_1(A_912))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_912)) ) ),
    inference(resolution,[status(thm)],[c_4150,c_2644])).

tff(c_4251,plain,
    ( r1_tarski('#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4089,c_4244])).

tff(c_4262,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4091,c_4251])).

tff(c_4264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4129,c_4262])).

tff(c_4265,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4108])).

tff(c_3099,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_3101,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3097,c_124])).

tff(c_3121,plain,
    ( '#skF_6' = '#skF_8'
    | ~ r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_3101,c_2])).

tff(c_3142,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3121])).

tff(c_3104,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3097,c_48])).

tff(c_3102,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3097,c_86])).

tff(c_3148,plain,(
    ! [A_722,B_723,C_724] :
      ( r2_hidden('#skF_1'(A_722,B_723,C_724),B_723)
      | r1_tarski(B_723,C_724)
      | ~ m1_subset_1(C_724,k1_zfmisc_1(A_722))
      | ~ m1_subset_1(B_723,k1_zfmisc_1(A_722)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3239,plain,(
    ! [C_735,A_736] :
      ( r1_tarski('#skF_6',C_735)
      | ~ m1_subset_1(C_735,k1_zfmisc_1(A_736))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_736)) ) ),
    inference(resolution,[status(thm)],[c_3148,c_2644])).

tff(c_3244,plain,
    ( r1_tarski('#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_3102,c_3239])).

tff(c_3254,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3104,c_3244])).

tff(c_3256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3142,c_3254])).

tff(c_3257,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3121])).

tff(c_3295,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3257,c_82])).

tff(c_3296,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_3099,c_3295])).

tff(c_3260,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3257,c_3257,c_3104])).

tff(c_3263,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3257,c_3097])).

tff(c_3782,plain,(
    ! [A_842,B_841,E_845,D_844,C_843] :
      ( k3_tmap_1(A_842,B_841,C_843,D_844,E_845) = k2_partfun1(u1_struct_0(C_843),u1_struct_0(B_841),E_845,u1_struct_0(D_844))
      | ~ m1_pre_topc(D_844,C_843)
      | ~ m1_subset_1(E_845,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_843),u1_struct_0(B_841))))
      | ~ v1_funct_2(E_845,u1_struct_0(C_843),u1_struct_0(B_841))
      | ~ v1_funct_1(E_845)
      | ~ m1_pre_topc(D_844,A_842)
      | ~ m1_pre_topc(C_843,A_842)
      | ~ l1_pre_topc(B_841)
      | ~ v2_pre_topc(B_841)
      | v2_struct_0(B_841)
      | ~ l1_pre_topc(A_842)
      | ~ v2_pre_topc(A_842)
      | v2_struct_0(A_842) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3787,plain,(
    ! [A_842,D_844,E_845] :
      ( k3_tmap_1(A_842,'#skF_3','#skF_2',D_844,E_845) = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_845,u1_struct_0(D_844))
      | ~ m1_pre_topc(D_844,'#skF_2')
      | ~ m1_subset_1(E_845,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_845,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_845)
      | ~ m1_pre_topc(D_844,A_842)
      | ~ m1_pre_topc('#skF_2',A_842)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_842)
      | ~ v2_pre_topc(A_842)
      | v2_struct_0(A_842) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3263,c_3782])).

tff(c_3795,plain,(
    ! [A_842,D_844,E_845] :
      ( k3_tmap_1(A_842,'#skF_3','#skF_2',D_844,E_845) = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_845,u1_struct_0(D_844))
      | ~ m1_pre_topc(D_844,'#skF_2')
      | ~ m1_subset_1(E_845,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_845,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_845)
      | ~ m1_pre_topc(D_844,A_842)
      | ~ m1_pre_topc('#skF_2',A_842)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_842)
      | ~ v2_pre_topc(A_842)
      | v2_struct_0(A_842) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_3787])).

tff(c_3930,plain,(
    ! [A_871,D_872,E_873] :
      ( k3_tmap_1(A_871,'#skF_3','#skF_2',D_872,E_873) = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_873,u1_struct_0(D_872))
      | ~ m1_pre_topc(D_872,'#skF_2')
      | ~ m1_subset_1(E_873,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_873,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_873)
      | ~ m1_pre_topc(D_872,A_871)
      | ~ m1_pre_topc('#skF_2',A_871)
      | ~ l1_pre_topc(A_871)
      | ~ v2_pre_topc(A_871)
      | v2_struct_0(A_871) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3795])).

tff(c_3932,plain,(
    ! [E_873] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_873,u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',E_873)
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | ~ m1_subset_1(E_873,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_873,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_873)
      | ~ m1_pre_topc('#skF_2','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_3930])).

tff(c_3937,plain,(
    ! [E_873] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_873,u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',E_873)
      | ~ m1_subset_1(E_873,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_873,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_873)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_83,c_58,c_3932])).

tff(c_4006,plain,(
    ! [E_888] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_888,u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',E_888)
      | ~ m1_subset_1(E_888,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_888,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_888) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3937])).

tff(c_3687,plain,(
    ! [A_817,B_818,C_819,D_820] :
      ( k2_partfun1(u1_struct_0(A_817),u1_struct_0(B_818),C_819,u1_struct_0(D_820)) = k2_tmap_1(A_817,B_818,C_819,D_820)
      | ~ m1_pre_topc(D_820,A_817)
      | ~ m1_subset_1(C_819,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_817),u1_struct_0(B_818))))
      | ~ v1_funct_2(C_819,u1_struct_0(A_817),u1_struct_0(B_818))
      | ~ v1_funct_1(C_819)
      | ~ l1_pre_topc(B_818)
      | ~ v2_pre_topc(B_818)
      | v2_struct_0(B_818)
      | ~ l1_pre_topc(A_817)
      | ~ v2_pre_topc(A_817)
      | v2_struct_0(A_817) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3692,plain,(
    ! [C_819,D_820] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),C_819,u1_struct_0(D_820)) = k2_tmap_1('#skF_2','#skF_3',C_819,D_820)
      | ~ m1_pre_topc(D_820,'#skF_2')
      | ~ m1_subset_1(C_819,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(C_819,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_819)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3263,c_3687])).

tff(c_3700,plain,(
    ! [C_819,D_820] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),C_819,u1_struct_0(D_820)) = k2_tmap_1('#skF_2','#skF_3',C_819,D_820)
      | ~ m1_pre_topc(D_820,'#skF_2')
      | ~ m1_subset_1(C_819,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(C_819,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_819)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_3692])).

tff(c_3701,plain,(
    ! [C_819,D_820] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),C_819,u1_struct_0(D_820)) = k2_tmap_1('#skF_2','#skF_3',C_819,D_820)
      | ~ m1_pre_topc(D_820,'#skF_2')
      | ~ m1_subset_1(C_819,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(C_819,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_819) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_3700])).

tff(c_4012,plain,(
    ! [E_888] :
      ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',E_888) = k2_tmap_1('#skF_2','#skF_3',E_888,'#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | ~ m1_subset_1(E_888,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_888,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_888)
      | ~ m1_subset_1(E_888,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_888,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_888) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4006,c_3701])).

tff(c_4026,plain,(
    ! [E_889] :
      ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',E_889) = k2_tmap_1('#skF_2','#skF_3',E_889,'#skF_4')
      | ~ m1_subset_1(E_889,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_889,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_889) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4012])).

tff(c_4029,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_85,c_4026])).

tff(c_4032,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3260,c_4029])).

tff(c_4033,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4032,c_3099])).

tff(c_4036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3296,c_4033])).

tff(c_4037,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_4311,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4265,c_4037])).

tff(c_4268,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4265,c_4265,c_4091])).

tff(c_4272,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4265,c_3097])).

tff(c_4855,plain,(
    ! [B_1029,D_1032,C_1031,E_1033,A_1030] :
      ( k3_tmap_1(A_1030,B_1029,C_1031,D_1032,E_1033) = k2_partfun1(u1_struct_0(C_1031),u1_struct_0(B_1029),E_1033,u1_struct_0(D_1032))
      | ~ m1_pre_topc(D_1032,C_1031)
      | ~ m1_subset_1(E_1033,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1031),u1_struct_0(B_1029))))
      | ~ v1_funct_2(E_1033,u1_struct_0(C_1031),u1_struct_0(B_1029))
      | ~ v1_funct_1(E_1033)
      | ~ m1_pre_topc(D_1032,A_1030)
      | ~ m1_pre_topc(C_1031,A_1030)
      | ~ l1_pre_topc(B_1029)
      | ~ v2_pre_topc(B_1029)
      | v2_struct_0(B_1029)
      | ~ l1_pre_topc(A_1030)
      | ~ v2_pre_topc(A_1030)
      | v2_struct_0(A_1030) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_4860,plain,(
    ! [A_1030,D_1032,E_1033] :
      ( k3_tmap_1(A_1030,'#skF_3','#skF_2',D_1032,E_1033) = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_1033,u1_struct_0(D_1032))
      | ~ m1_pre_topc(D_1032,'#skF_2')
      | ~ m1_subset_1(E_1033,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_1033,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_1033)
      | ~ m1_pre_topc(D_1032,A_1030)
      | ~ m1_pre_topc('#skF_2',A_1030)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_1030)
      | ~ v2_pre_topc(A_1030)
      | v2_struct_0(A_1030) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4272,c_4855])).

tff(c_4868,plain,(
    ! [A_1030,D_1032,E_1033] :
      ( k3_tmap_1(A_1030,'#skF_3','#skF_2',D_1032,E_1033) = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_1033,u1_struct_0(D_1032))
      | ~ m1_pre_topc(D_1032,'#skF_2')
      | ~ m1_subset_1(E_1033,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_1033,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_1033)
      | ~ m1_pre_topc(D_1032,A_1030)
      | ~ m1_pre_topc('#skF_2',A_1030)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_1030)
      | ~ v2_pre_topc(A_1030)
      | v2_struct_0(A_1030) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_4860])).

tff(c_4982,plain,(
    ! [A_1057,D_1058,E_1059] :
      ( k3_tmap_1(A_1057,'#skF_3','#skF_2',D_1058,E_1059) = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_1059,u1_struct_0(D_1058))
      | ~ m1_pre_topc(D_1058,'#skF_2')
      | ~ m1_subset_1(E_1059,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_1059,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_1059)
      | ~ m1_pre_topc(D_1058,A_1057)
      | ~ m1_pre_topc('#skF_2',A_1057)
      | ~ l1_pre_topc(A_1057)
      | ~ v2_pre_topc(A_1057)
      | v2_struct_0(A_1057) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4868])).

tff(c_4984,plain,(
    ! [E_1059] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_1059,u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',E_1059)
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | ~ m1_subset_1(E_1059,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_1059,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_1059)
      | ~ m1_pre_topc('#skF_2','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_4982])).

tff(c_4989,plain,(
    ! [E_1059] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_1059,u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',E_1059)
      | ~ m1_subset_1(E_1059,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_1059,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_1059)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_83,c_58,c_4984])).

tff(c_4995,plain,(
    ! [E_1060] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_1060,u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',E_1060)
      | ~ m1_subset_1(E_1060,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_1060,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_1060) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4989])).

tff(c_4737,plain,(
    ! [A_1003,B_1004,C_1005,D_1006] :
      ( k2_partfun1(u1_struct_0(A_1003),u1_struct_0(B_1004),C_1005,u1_struct_0(D_1006)) = k2_tmap_1(A_1003,B_1004,C_1005,D_1006)
      | ~ m1_pre_topc(D_1006,A_1003)
      | ~ m1_subset_1(C_1005,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1003),u1_struct_0(B_1004))))
      | ~ v1_funct_2(C_1005,u1_struct_0(A_1003),u1_struct_0(B_1004))
      | ~ v1_funct_1(C_1005)
      | ~ l1_pre_topc(B_1004)
      | ~ v2_pre_topc(B_1004)
      | v2_struct_0(B_1004)
      | ~ l1_pre_topc(A_1003)
      | ~ v2_pre_topc(A_1003)
      | v2_struct_0(A_1003) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4742,plain,(
    ! [C_1005,D_1006] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),C_1005,u1_struct_0(D_1006)) = k2_tmap_1('#skF_2','#skF_3',C_1005,D_1006)
      | ~ m1_pre_topc(D_1006,'#skF_2')
      | ~ m1_subset_1(C_1005,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(C_1005,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_1005)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4272,c_4737])).

tff(c_4750,plain,(
    ! [C_1005,D_1006] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),C_1005,u1_struct_0(D_1006)) = k2_tmap_1('#skF_2','#skF_3',C_1005,D_1006)
      | ~ m1_pre_topc(D_1006,'#skF_2')
      | ~ m1_subset_1(C_1005,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(C_1005,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_1005)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_4742])).

tff(c_4751,plain,(
    ! [C_1005,D_1006] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),C_1005,u1_struct_0(D_1006)) = k2_tmap_1('#skF_2','#skF_3',C_1005,D_1006)
      | ~ m1_pre_topc(D_1006,'#skF_2')
      | ~ m1_subset_1(C_1005,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(C_1005,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_1005) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_4750])).

tff(c_5001,plain,(
    ! [E_1060] :
      ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',E_1060) = k2_tmap_1('#skF_2','#skF_3',E_1060,'#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | ~ m1_subset_1(E_1060,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_1060,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_1060)
      | ~ m1_subset_1(E_1060,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_1060,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_1060) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4995,c_4751])).

tff(c_5015,plain,(
    ! [E_1061] :
      ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',E_1061) = k2_tmap_1('#skF_2','#skF_3',E_1061,'#skF_4')
      | ~ m1_subset_1(E_1061,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_1061,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_1061) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5001])).

tff(c_5018,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_85,c_5015])).

tff(c_5021,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4268,c_5018])).

tff(c_4038,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_5022,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5021,c_4038])).

tff(c_5024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4311,c_5022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:25:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.96/2.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.11/2.42  
% 7.11/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.11/2.42  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 7.11/2.42  
% 7.11/2.42  %Foreground sorts:
% 7.11/2.42  
% 7.11/2.42  
% 7.11/2.42  %Background operators:
% 7.11/2.42  
% 7.11/2.42  
% 7.11/2.42  %Foreground operators:
% 7.11/2.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.11/2.42  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.11/2.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.11/2.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.11/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.11/2.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.11/2.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.11/2.42  tff('#skF_7', type, '#skF_7': $i).
% 7.11/2.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.11/2.42  tff('#skF_5', type, '#skF_5': $i).
% 7.11/2.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.11/2.42  tff('#skF_6', type, '#skF_6': $i).
% 7.11/2.42  tff('#skF_2', type, '#skF_2': $i).
% 7.11/2.42  tff('#skF_3', type, '#skF_3': $i).
% 7.11/2.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.11/2.42  tff('#skF_8', type, '#skF_8': $i).
% 7.11/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.11/2.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.11/2.42  tff('#skF_4', type, '#skF_4': $i).
% 7.11/2.42  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 7.11/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.11/2.42  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.11/2.42  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.11/2.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.11/2.42  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.11/2.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.11/2.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.11/2.42  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.11/2.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.11/2.42  
% 7.27/2.45  tff(f_213, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_tmap_1)).
% 7.27/2.45  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.27/2.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.27/2.45  tff(f_63, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.27/2.45  tff(f_85, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 7.27/2.45  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 7.27/2.45  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 7.27/2.45  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.27/2.45  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 7.27/2.45  tff(c_34, plain, ('#skF_5'='#skF_2'), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_36, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_86, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 7.27/2.45  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.27/2.45  tff(c_124, plain, (r1_tarski('#skF_8', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_86, c_14])).
% 7.27/2.45  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.27/2.45  tff(c_140, plain, (k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))='#skF_8' | ~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')), '#skF_8')), inference(resolution, [status(thm)], [c_124, c_2])).
% 7.27/2.45  tff(c_2709, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')), '#skF_8')), inference(splitLeft, [status(thm)], [c_140])).
% 7.27/2.45  tff(c_1241, plain, (![C_424, B_425, A_426]: (v1_xboole_0(C_424) | ~m1_subset_1(C_424, k1_zfmisc_1(k2_zfmisc_1(B_425, A_426))) | ~v1_xboole_0(A_426))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.27/2.45  tff(c_1255, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_86, c_1241])).
% 7.27/2.45  tff(c_1266, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1255])).
% 7.27/2.45  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_50, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_40, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_38, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_85, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 7.27/2.45  tff(c_32, plain, (r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_87, plain, (r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32])).
% 7.27/2.45  tff(c_2290, plain, (![C_594, E_595, F_598, B_596, A_597, D_599]: (F_598=E_595 | ~r1_funct_2(A_597, B_596, C_594, D_599, E_595, F_598) | ~m1_subset_1(F_598, k1_zfmisc_1(k2_zfmisc_1(C_594, D_599))) | ~v1_funct_2(F_598, C_594, D_599) | ~v1_funct_1(F_598) | ~m1_subset_1(E_595, k1_zfmisc_1(k2_zfmisc_1(A_597, B_596))) | ~v1_funct_2(E_595, A_597, B_596) | ~v1_funct_1(E_595) | v1_xboole_0(D_599) | v1_xboole_0(B_596))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.27/2.45  tff(c_2292, plain, ('#skF_6'='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_87, c_2290])).
% 7.27/2.45  tff(c_2295, plain, ('#skF_6'='#skF_8' | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_40, c_85, c_86, c_2292])).
% 7.27/2.45  tff(c_2296, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_1266, c_2295])).
% 7.27/2.45  tff(c_1809, plain, (![C_513, D_518, B_515, A_516, F_517, E_514]: (F_517=E_514 | ~r1_funct_2(A_516, B_515, C_513, D_518, E_514, F_517) | ~m1_subset_1(F_517, k1_zfmisc_1(k2_zfmisc_1(C_513, D_518))) | ~v1_funct_2(F_517, C_513, D_518) | ~v1_funct_1(F_517) | ~m1_subset_1(E_514, k1_zfmisc_1(k2_zfmisc_1(A_516, B_515))) | ~v1_funct_2(E_514, A_516, B_515) | ~v1_funct_1(E_514) | v1_xboole_0(D_518) | v1_xboole_0(B_515))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.27/2.45  tff(c_1811, plain, ('#skF_6'='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_87, c_1809])).
% 7.27/2.45  tff(c_1814, plain, ('#skF_6'='#skF_8' | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_40, c_85, c_86, c_1811])).
% 7.27/2.45  tff(c_1815, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_1266, c_1814])).
% 7.27/2.45  tff(c_80, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_8'), '#skF_7') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_82, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_80])).
% 7.27/2.45  tff(c_1608, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(splitLeft, [status(thm)], [c_82])).
% 7.27/2.45  tff(c_1818, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1815, c_1608])).
% 7.27/2.45  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_83, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_54])).
% 7.27/2.45  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_2039, plain, (![C_555, B_553, D_556, E_557, A_554]: (k3_tmap_1(A_554, B_553, C_555, D_556, E_557)=k2_partfun1(u1_struct_0(C_555), u1_struct_0(B_553), E_557, u1_struct_0(D_556)) | ~m1_pre_topc(D_556, C_555) | ~m1_subset_1(E_557, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_555), u1_struct_0(B_553)))) | ~v1_funct_2(E_557, u1_struct_0(C_555), u1_struct_0(B_553)) | ~v1_funct_1(E_557) | ~m1_pre_topc(D_556, A_554) | ~m1_pre_topc(C_555, A_554) | ~l1_pre_topc(B_553) | ~v2_pre_topc(B_553) | v2_struct_0(B_553) | ~l1_pre_topc(A_554) | ~v2_pre_topc(A_554) | v2_struct_0(A_554))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.27/2.45  tff(c_2046, plain, (![A_554, D_556]: (k3_tmap_1(A_554, '#skF_3', '#skF_2', D_556, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_556)) | ~m1_pre_topc(D_556, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc(D_556, A_554) | ~m1_pre_topc('#skF_2', A_554) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_554) | ~v2_pre_topc(A_554) | v2_struct_0(A_554))), inference(resolution, [status(thm)], [c_86, c_2039])).
% 7.27/2.45  tff(c_2056, plain, (![A_554, D_556]: (k3_tmap_1(A_554, '#skF_3', '#skF_2', D_556, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_556)) | ~m1_pre_topc(D_556, '#skF_2') | ~m1_pre_topc(D_556, A_554) | ~m1_pre_topc('#skF_2', A_554) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_554) | ~v2_pre_topc(A_554) | v2_struct_0(A_554))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_40, c_85, c_2046])).
% 7.27/2.45  tff(c_2077, plain, (![A_562, D_563]: (k3_tmap_1(A_562, '#skF_3', '#skF_2', D_563, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_563)) | ~m1_pre_topc(D_563, '#skF_2') | ~m1_pre_topc(D_563, A_562) | ~m1_pre_topc('#skF_2', A_562) | ~l1_pre_topc(A_562) | ~v2_pre_topc(A_562) | v2_struct_0(A_562))), inference(negUnitSimplification, [status(thm)], [c_66, c_2056])).
% 7.27/2.45  tff(c_2079, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_2077])).
% 7.27/2.45  tff(c_2084, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_83, c_58, c_2079])).
% 7.27/2.45  tff(c_2085, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_72, c_2084])).
% 7.27/2.45  tff(c_1897, plain, (![A_530, B_531, C_532, D_533]: (k2_partfun1(u1_struct_0(A_530), u1_struct_0(B_531), C_532, u1_struct_0(D_533))=k2_tmap_1(A_530, B_531, C_532, D_533) | ~m1_pre_topc(D_533, A_530) | ~m1_subset_1(C_532, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_530), u1_struct_0(B_531)))) | ~v1_funct_2(C_532, u1_struct_0(A_530), u1_struct_0(B_531)) | ~v1_funct_1(C_532) | ~l1_pre_topc(B_531) | ~v2_pre_topc(B_531) | v2_struct_0(B_531) | ~l1_pre_topc(A_530) | ~v2_pre_topc(A_530) | v2_struct_0(A_530))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.27/2.45  tff(c_1904, plain, (![D_533]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_533))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_533) | ~m1_pre_topc(D_533, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_86, c_1897])).
% 7.27/2.45  tff(c_1914, plain, (![D_533]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_533))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_533) | ~m1_pre_topc(D_533, '#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_40, c_85, c_1904])).
% 7.27/2.45  tff(c_1915, plain, (![D_533]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_533))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_533) | ~m1_pre_topc(D_533, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_1914])).
% 7.27/2.45  tff(c_2093, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2085, c_1915])).
% 7.27/2.45  tff(c_2100, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2093])).
% 7.27/2.45  tff(c_74, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.27/2.45  tff(c_84, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_74])).
% 7.27/2.45  tff(c_1658, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1608, c_84])).
% 7.27/2.45  tff(c_2105, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2100, c_1658])).
% 7.27/2.45  tff(c_2108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1818, c_2105])).
% 7.27/2.45  tff(c_2110, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(splitRight, [status(thm)], [c_82])).
% 7.27/2.45  tff(c_2299, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2296, c_2110])).
% 7.27/2.45  tff(c_2527, plain, (![A_634, B_633, D_636, C_635, E_637]: (k3_tmap_1(A_634, B_633, C_635, D_636, E_637)=k2_partfun1(u1_struct_0(C_635), u1_struct_0(B_633), E_637, u1_struct_0(D_636)) | ~m1_pre_topc(D_636, C_635) | ~m1_subset_1(E_637, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_635), u1_struct_0(B_633)))) | ~v1_funct_2(E_637, u1_struct_0(C_635), u1_struct_0(B_633)) | ~v1_funct_1(E_637) | ~m1_pre_topc(D_636, A_634) | ~m1_pre_topc(C_635, A_634) | ~l1_pre_topc(B_633) | ~v2_pre_topc(B_633) | v2_struct_0(B_633) | ~l1_pre_topc(A_634) | ~v2_pre_topc(A_634) | v2_struct_0(A_634))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.27/2.45  tff(c_2534, plain, (![A_634, D_636]: (k3_tmap_1(A_634, '#skF_3', '#skF_2', D_636, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_636)) | ~m1_pre_topc(D_636, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc(D_636, A_634) | ~m1_pre_topc('#skF_2', A_634) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_634) | ~v2_pre_topc(A_634) | v2_struct_0(A_634))), inference(resolution, [status(thm)], [c_86, c_2527])).
% 7.27/2.45  tff(c_2544, plain, (![A_634, D_636]: (k3_tmap_1(A_634, '#skF_3', '#skF_2', D_636, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_636)) | ~m1_pre_topc(D_636, '#skF_2') | ~m1_pre_topc(D_636, A_634) | ~m1_pre_topc('#skF_2', A_634) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_634) | ~v2_pre_topc(A_634) | v2_struct_0(A_634))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_40, c_85, c_2534])).
% 7.27/2.45  tff(c_2574, plain, (![A_644, D_645]: (k3_tmap_1(A_644, '#skF_3', '#skF_2', D_645, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_645)) | ~m1_pre_topc(D_645, '#skF_2') | ~m1_pre_topc(D_645, A_644) | ~m1_pre_topc('#skF_2', A_644) | ~l1_pre_topc(A_644) | ~v2_pre_topc(A_644) | v2_struct_0(A_644))), inference(negUnitSimplification, [status(thm)], [c_66, c_2544])).
% 7.27/2.45  tff(c_2576, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_2574])).
% 7.27/2.45  tff(c_2581, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_83, c_58, c_2576])).
% 7.27/2.45  tff(c_2582, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_72, c_2581])).
% 7.27/2.45  tff(c_2388, plain, (![A_608, B_609, C_610, D_611]: (k2_partfun1(u1_struct_0(A_608), u1_struct_0(B_609), C_610, u1_struct_0(D_611))=k2_tmap_1(A_608, B_609, C_610, D_611) | ~m1_pre_topc(D_611, A_608) | ~m1_subset_1(C_610, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_608), u1_struct_0(B_609)))) | ~v1_funct_2(C_610, u1_struct_0(A_608), u1_struct_0(B_609)) | ~v1_funct_1(C_610) | ~l1_pre_topc(B_609) | ~v2_pre_topc(B_609) | v2_struct_0(B_609) | ~l1_pre_topc(A_608) | ~v2_pre_topc(A_608) | v2_struct_0(A_608))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.27/2.45  tff(c_2395, plain, (![D_611]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_611))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_611) | ~m1_pre_topc(D_611, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_86, c_2388])).
% 7.27/2.45  tff(c_2405, plain, (![D_611]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_611))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_611) | ~m1_pre_topc(D_611, '#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_40, c_85, c_2395])).
% 7.27/2.45  tff(c_2406, plain, (![D_611]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_611))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_611) | ~m1_pre_topc(D_611, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_2405])).
% 7.27/2.45  tff(c_2590, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2582, c_2406])).
% 7.27/2.45  tff(c_2597, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2590])).
% 7.27/2.45  tff(c_2109, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_82])).
% 7.27/2.45  tff(c_2602, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2597, c_2109])).
% 7.27/2.45  tff(c_2604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2299, c_2602])).
% 7.27/2.45  tff(c_2606, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1255])).
% 7.27/2.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.27/2.45  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.27/2.45  tff(c_2612, plain, (![A_649, A_650, B_651]: (v1_xboole_0(A_649) | ~v1_xboole_0(A_650) | ~r1_tarski(A_649, k2_zfmisc_1(B_651, A_650)))), inference(resolution, [status(thm)], [c_16, c_1241])).
% 7.27/2.45  tff(c_2636, plain, (![B_652, A_653]: (v1_xboole_0(k2_zfmisc_1(B_652, A_653)) | ~v1_xboole_0(A_653))), inference(resolution, [status(thm)], [c_6, c_2612])).
% 7.27/2.45  tff(c_125, plain, (![C_205, B_206, A_207]: (~v1_xboole_0(C_205) | ~m1_subset_1(B_206, k1_zfmisc_1(C_205)) | ~r2_hidden(A_207, B_206))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.27/2.45  tff(c_136, plain, (![A_207]: (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~r2_hidden(A_207, '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_125])).
% 7.27/2.45  tff(c_142, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_136])).
% 7.27/2.45  tff(c_2639, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2636, c_142])).
% 7.27/2.45  tff(c_2643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2606, c_2639])).
% 7.27/2.45  tff(c_2645, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_136])).
% 7.27/2.45  tff(c_2712, plain, (![A_671, B_672, C_673]: (r2_hidden('#skF_1'(A_671, B_672, C_673), B_672) | r1_tarski(B_672, C_673) | ~m1_subset_1(C_673, k1_zfmisc_1(A_671)) | ~m1_subset_1(B_672, k1_zfmisc_1(A_671)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.27/2.45  tff(c_137, plain, (![B_11, A_207, A_10]: (~v1_xboole_0(B_11) | ~r2_hidden(A_207, A_10) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_16, c_125])).
% 7.27/2.45  tff(c_2903, plain, (![B_691, B_692, C_693, A_694]: (~v1_xboole_0(B_691) | ~r1_tarski(B_692, B_691) | r1_tarski(B_692, C_693) | ~m1_subset_1(C_693, k1_zfmisc_1(A_694)) | ~m1_subset_1(B_692, k1_zfmisc_1(A_694)))), inference(resolution, [status(thm)], [c_2712, c_137])).
% 7.27/2.45  tff(c_2926, plain, (![B_698, C_699, A_700]: (~v1_xboole_0(B_698) | r1_tarski(B_698, C_699) | ~m1_subset_1(C_699, k1_zfmisc_1(A_700)) | ~m1_subset_1(B_698, k1_zfmisc_1(A_700)))), inference(resolution, [status(thm)], [c_6, c_2903])).
% 7.27/2.45  tff(c_2940, plain, (![B_701, A_702, B_703]: (~v1_xboole_0(B_701) | r1_tarski(B_701, A_702) | ~m1_subset_1(B_701, k1_zfmisc_1(B_703)) | ~r1_tarski(A_702, B_703))), inference(resolution, [status(thm)], [c_16, c_2926])).
% 7.27/2.45  tff(c_2954, plain, (![A_704, A_705, B_706]: (~v1_xboole_0(A_704) | r1_tarski(A_704, A_705) | ~r1_tarski(A_705, B_706) | ~r1_tarski(A_704, B_706))), inference(resolution, [status(thm)], [c_16, c_2940])).
% 7.27/2.45  tff(c_3001, plain, (![A_713]: (~v1_xboole_0(A_713) | r1_tarski(A_713, '#skF_8') | ~r1_tarski(A_713, k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_124, c_2954])).
% 7.27/2.45  tff(c_3008, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')), '#skF_8')), inference(resolution, [status(thm)], [c_6, c_3001])).
% 7.27/2.45  tff(c_3013, plain, (r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2645, c_3008])).
% 7.27/2.45  tff(c_3015, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2709, c_3013])).
% 7.27/2.45  tff(c_3016, plain, (k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))='#skF_8'), inference(splitRight, [status(thm)], [c_140])).
% 7.27/2.45  tff(c_103, plain, (r1_tarski('#skF_6', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_48, c_14])).
% 7.27/2.45  tff(c_108, plain, (![B_203, A_204]: (B_203=A_204 | ~r1_tarski(B_203, A_204) | ~r1_tarski(A_204, B_203))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.27/2.45  tff(c_116, plain, (k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))='#skF_6' | ~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')), '#skF_6')), inference(resolution, [status(thm)], [c_103, c_108])).
% 7.27/2.45  tff(c_2707, plain, (~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')), '#skF_6')), inference(splitLeft, [status(thm)], [c_116])).
% 7.27/2.45  tff(c_3018, plain, (~r1_tarski('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3016, c_2707])).
% 7.27/2.45  tff(c_3021, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3016, c_86])).
% 7.27/2.45  tff(c_3023, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3016, c_48])).
% 7.27/2.45  tff(c_3059, plain, (![A_714, B_715, C_716]: (r2_hidden('#skF_1'(A_714, B_715, C_716), B_715) | r1_tarski(B_715, C_716) | ~m1_subset_1(C_716, k1_zfmisc_1(A_714)) | ~m1_subset_1(B_715, k1_zfmisc_1(A_714)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.27/2.45  tff(c_134, plain, (![A_207]: (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~r2_hidden(A_207, '#skF_8'))), inference(resolution, [status(thm)], [c_86, c_125])).
% 7.27/2.45  tff(c_2649, plain, (![A_207]: (~r2_hidden(A_207, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2645, c_134])).
% 7.27/2.45  tff(c_3080, plain, (![C_717, A_718]: (r1_tarski('#skF_8', C_717) | ~m1_subset_1(C_717, k1_zfmisc_1(A_718)) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_718)))), inference(resolution, [status(thm)], [c_3059, c_2649])).
% 7.27/2.45  tff(c_3084, plain, (r1_tarski('#skF_8', '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_3023, c_3080])).
% 7.27/2.45  tff(c_3094, plain, (r1_tarski('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3021, c_3084])).
% 7.27/2.45  tff(c_3096, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3018, c_3094])).
% 7.27/2.45  tff(c_3097, plain, (k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))='#skF_6'), inference(splitRight, [status(thm)], [c_116])).
% 7.27/2.45  tff(c_4088, plain, (r1_tarski('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3097, c_124])).
% 7.27/2.45  tff(c_4108, plain, ('#skF_6'='#skF_8' | ~r1_tarski('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_4088, c_2])).
% 7.27/2.45  tff(c_4129, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_4108])).
% 7.27/2.45  tff(c_4091, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3097, c_48])).
% 7.27/2.45  tff(c_4089, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3097, c_86])).
% 7.27/2.45  tff(c_4150, plain, (![A_896, B_897, C_898]: (r2_hidden('#skF_1'(A_896, B_897, C_898), B_897) | r1_tarski(B_897, C_898) | ~m1_subset_1(C_898, k1_zfmisc_1(A_896)) | ~m1_subset_1(B_897, k1_zfmisc_1(A_896)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.27/2.45  tff(c_2644, plain, (![A_207]: (~r2_hidden(A_207, '#skF_6'))), inference(splitRight, [status(thm)], [c_136])).
% 7.27/2.45  tff(c_4244, plain, (![C_911, A_912]: (r1_tarski('#skF_6', C_911) | ~m1_subset_1(C_911, k1_zfmisc_1(A_912)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_912)))), inference(resolution, [status(thm)], [c_4150, c_2644])).
% 7.27/2.45  tff(c_4251, plain, (r1_tarski('#skF_6', '#skF_8') | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_4089, c_4244])).
% 7.27/2.45  tff(c_4262, plain, (r1_tarski('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4091, c_4251])).
% 7.27/2.45  tff(c_4264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4129, c_4262])).
% 7.27/2.45  tff(c_4265, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_4108])).
% 7.27/2.45  tff(c_3099, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_84])).
% 7.27/2.45  tff(c_3101, plain, (r1_tarski('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3097, c_124])).
% 7.27/2.45  tff(c_3121, plain, ('#skF_6'='#skF_8' | ~r1_tarski('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_3101, c_2])).
% 7.27/2.45  tff(c_3142, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_3121])).
% 7.27/2.45  tff(c_3104, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3097, c_48])).
% 7.27/2.45  tff(c_3102, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3097, c_86])).
% 7.27/2.45  tff(c_3148, plain, (![A_722, B_723, C_724]: (r2_hidden('#skF_1'(A_722, B_723, C_724), B_723) | r1_tarski(B_723, C_724) | ~m1_subset_1(C_724, k1_zfmisc_1(A_722)) | ~m1_subset_1(B_723, k1_zfmisc_1(A_722)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.27/2.45  tff(c_3239, plain, (![C_735, A_736]: (r1_tarski('#skF_6', C_735) | ~m1_subset_1(C_735, k1_zfmisc_1(A_736)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_736)))), inference(resolution, [status(thm)], [c_3148, c_2644])).
% 7.27/2.45  tff(c_3244, plain, (r1_tarski('#skF_6', '#skF_8') | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_3102, c_3239])).
% 7.27/2.45  tff(c_3254, plain, (r1_tarski('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3104, c_3244])).
% 7.27/2.45  tff(c_3256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3142, c_3254])).
% 7.27/2.45  tff(c_3257, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_3121])).
% 7.27/2.45  tff(c_3295, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3257, c_82])).
% 7.27/2.45  tff(c_3296, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_3099, c_3295])).
% 7.27/2.45  tff(c_3260, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3257, c_3257, c_3104])).
% 7.27/2.45  tff(c_3263, plain, (k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3257, c_3097])).
% 7.27/2.45  tff(c_3782, plain, (![A_842, B_841, E_845, D_844, C_843]: (k3_tmap_1(A_842, B_841, C_843, D_844, E_845)=k2_partfun1(u1_struct_0(C_843), u1_struct_0(B_841), E_845, u1_struct_0(D_844)) | ~m1_pre_topc(D_844, C_843) | ~m1_subset_1(E_845, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_843), u1_struct_0(B_841)))) | ~v1_funct_2(E_845, u1_struct_0(C_843), u1_struct_0(B_841)) | ~v1_funct_1(E_845) | ~m1_pre_topc(D_844, A_842) | ~m1_pre_topc(C_843, A_842) | ~l1_pre_topc(B_841) | ~v2_pre_topc(B_841) | v2_struct_0(B_841) | ~l1_pre_topc(A_842) | ~v2_pre_topc(A_842) | v2_struct_0(A_842))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.27/2.45  tff(c_3787, plain, (![A_842, D_844, E_845]: (k3_tmap_1(A_842, '#skF_3', '#skF_2', D_844, E_845)=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_845, u1_struct_0(D_844)) | ~m1_pre_topc(D_844, '#skF_2') | ~m1_subset_1(E_845, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_845, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_845) | ~m1_pre_topc(D_844, A_842) | ~m1_pre_topc('#skF_2', A_842) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_842) | ~v2_pre_topc(A_842) | v2_struct_0(A_842))), inference(superposition, [status(thm), theory('equality')], [c_3263, c_3782])).
% 7.27/2.45  tff(c_3795, plain, (![A_842, D_844, E_845]: (k3_tmap_1(A_842, '#skF_3', '#skF_2', D_844, E_845)=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_845, u1_struct_0(D_844)) | ~m1_pre_topc(D_844, '#skF_2') | ~m1_subset_1(E_845, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_845, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_845) | ~m1_pre_topc(D_844, A_842) | ~m1_pre_topc('#skF_2', A_842) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_842) | ~v2_pre_topc(A_842) | v2_struct_0(A_842))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_3787])).
% 7.27/2.45  tff(c_3930, plain, (![A_871, D_872, E_873]: (k3_tmap_1(A_871, '#skF_3', '#skF_2', D_872, E_873)=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_873, u1_struct_0(D_872)) | ~m1_pre_topc(D_872, '#skF_2') | ~m1_subset_1(E_873, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_873, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_873) | ~m1_pre_topc(D_872, A_871) | ~m1_pre_topc('#skF_2', A_871) | ~l1_pre_topc(A_871) | ~v2_pre_topc(A_871) | v2_struct_0(A_871))), inference(negUnitSimplification, [status(thm)], [c_66, c_3795])).
% 7.27/2.45  tff(c_3932, plain, (![E_873]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_873, u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', E_873) | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(E_873, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_873, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_873) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_3930])).
% 7.27/2.45  tff(c_3937, plain, (![E_873]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_873, u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', E_873) | ~m1_subset_1(E_873, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_873, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_873) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_83, c_58, c_3932])).
% 7.27/2.45  tff(c_4006, plain, (![E_888]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_888, u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', E_888) | ~m1_subset_1(E_888, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_888, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_888))), inference(negUnitSimplification, [status(thm)], [c_72, c_3937])).
% 7.27/2.45  tff(c_3687, plain, (![A_817, B_818, C_819, D_820]: (k2_partfun1(u1_struct_0(A_817), u1_struct_0(B_818), C_819, u1_struct_0(D_820))=k2_tmap_1(A_817, B_818, C_819, D_820) | ~m1_pre_topc(D_820, A_817) | ~m1_subset_1(C_819, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_817), u1_struct_0(B_818)))) | ~v1_funct_2(C_819, u1_struct_0(A_817), u1_struct_0(B_818)) | ~v1_funct_1(C_819) | ~l1_pre_topc(B_818) | ~v2_pre_topc(B_818) | v2_struct_0(B_818) | ~l1_pre_topc(A_817) | ~v2_pre_topc(A_817) | v2_struct_0(A_817))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.27/2.45  tff(c_3692, plain, (![C_819, D_820]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), C_819, u1_struct_0(D_820))=k2_tmap_1('#skF_2', '#skF_3', C_819, D_820) | ~m1_pre_topc(D_820, '#skF_2') | ~m1_subset_1(C_819, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(C_819, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_819) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3263, c_3687])).
% 7.27/2.45  tff(c_3700, plain, (![C_819, D_820]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), C_819, u1_struct_0(D_820))=k2_tmap_1('#skF_2', '#skF_3', C_819, D_820) | ~m1_pre_topc(D_820, '#skF_2') | ~m1_subset_1(C_819, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(C_819, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_819) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_3692])).
% 7.27/2.45  tff(c_3701, plain, (![C_819, D_820]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), C_819, u1_struct_0(D_820))=k2_tmap_1('#skF_2', '#skF_3', C_819, D_820) | ~m1_pre_topc(D_820, '#skF_2') | ~m1_subset_1(C_819, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(C_819, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_819))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_3700])).
% 7.27/2.45  tff(c_4012, plain, (![E_888]: (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', E_888)=k2_tmap_1('#skF_2', '#skF_3', E_888, '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(E_888, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_888, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_888) | ~m1_subset_1(E_888, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_888, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_888))), inference(superposition, [status(thm), theory('equality')], [c_4006, c_3701])).
% 7.27/2.45  tff(c_4026, plain, (![E_889]: (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', E_889)=k2_tmap_1('#skF_2', '#skF_3', E_889, '#skF_4') | ~m1_subset_1(E_889, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_889, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_889))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4012])).
% 7.27/2.45  tff(c_4029, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4') | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_85, c_4026])).
% 7.27/2.45  tff(c_4032, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3260, c_4029])).
% 7.27/2.45  tff(c_4033, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4032, c_3099])).
% 7.27/2.45  tff(c_4036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3296, c_4033])).
% 7.27/2.45  tff(c_4037, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(splitRight, [status(thm)], [c_84])).
% 7.27/2.45  tff(c_4311, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4265, c_4037])).
% 7.27/2.45  tff(c_4268, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4265, c_4265, c_4091])).
% 7.27/2.45  tff(c_4272, plain, (k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4265, c_3097])).
% 7.27/2.45  tff(c_4855, plain, (![B_1029, D_1032, C_1031, E_1033, A_1030]: (k3_tmap_1(A_1030, B_1029, C_1031, D_1032, E_1033)=k2_partfun1(u1_struct_0(C_1031), u1_struct_0(B_1029), E_1033, u1_struct_0(D_1032)) | ~m1_pre_topc(D_1032, C_1031) | ~m1_subset_1(E_1033, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1031), u1_struct_0(B_1029)))) | ~v1_funct_2(E_1033, u1_struct_0(C_1031), u1_struct_0(B_1029)) | ~v1_funct_1(E_1033) | ~m1_pre_topc(D_1032, A_1030) | ~m1_pre_topc(C_1031, A_1030) | ~l1_pre_topc(B_1029) | ~v2_pre_topc(B_1029) | v2_struct_0(B_1029) | ~l1_pre_topc(A_1030) | ~v2_pre_topc(A_1030) | v2_struct_0(A_1030))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.27/2.45  tff(c_4860, plain, (![A_1030, D_1032, E_1033]: (k3_tmap_1(A_1030, '#skF_3', '#skF_2', D_1032, E_1033)=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_1033, u1_struct_0(D_1032)) | ~m1_pre_topc(D_1032, '#skF_2') | ~m1_subset_1(E_1033, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_1033, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_1033) | ~m1_pre_topc(D_1032, A_1030) | ~m1_pre_topc('#skF_2', A_1030) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_1030) | ~v2_pre_topc(A_1030) | v2_struct_0(A_1030))), inference(superposition, [status(thm), theory('equality')], [c_4272, c_4855])).
% 7.27/2.45  tff(c_4868, plain, (![A_1030, D_1032, E_1033]: (k3_tmap_1(A_1030, '#skF_3', '#skF_2', D_1032, E_1033)=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_1033, u1_struct_0(D_1032)) | ~m1_pre_topc(D_1032, '#skF_2') | ~m1_subset_1(E_1033, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_1033, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_1033) | ~m1_pre_topc(D_1032, A_1030) | ~m1_pre_topc('#skF_2', A_1030) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_1030) | ~v2_pre_topc(A_1030) | v2_struct_0(A_1030))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_4860])).
% 7.27/2.45  tff(c_4982, plain, (![A_1057, D_1058, E_1059]: (k3_tmap_1(A_1057, '#skF_3', '#skF_2', D_1058, E_1059)=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_1059, u1_struct_0(D_1058)) | ~m1_pre_topc(D_1058, '#skF_2') | ~m1_subset_1(E_1059, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_1059, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_1059) | ~m1_pre_topc(D_1058, A_1057) | ~m1_pre_topc('#skF_2', A_1057) | ~l1_pre_topc(A_1057) | ~v2_pre_topc(A_1057) | v2_struct_0(A_1057))), inference(negUnitSimplification, [status(thm)], [c_66, c_4868])).
% 7.27/2.45  tff(c_4984, plain, (![E_1059]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_1059, u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', E_1059) | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(E_1059, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_1059, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_1059) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_4982])).
% 7.27/2.45  tff(c_4989, plain, (![E_1059]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_1059, u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', E_1059) | ~m1_subset_1(E_1059, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_1059, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_1059) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_83, c_58, c_4984])).
% 7.27/2.45  tff(c_4995, plain, (![E_1060]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_1060, u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', E_1060) | ~m1_subset_1(E_1060, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_1060, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_1060))), inference(negUnitSimplification, [status(thm)], [c_72, c_4989])).
% 7.27/2.45  tff(c_4737, plain, (![A_1003, B_1004, C_1005, D_1006]: (k2_partfun1(u1_struct_0(A_1003), u1_struct_0(B_1004), C_1005, u1_struct_0(D_1006))=k2_tmap_1(A_1003, B_1004, C_1005, D_1006) | ~m1_pre_topc(D_1006, A_1003) | ~m1_subset_1(C_1005, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1003), u1_struct_0(B_1004)))) | ~v1_funct_2(C_1005, u1_struct_0(A_1003), u1_struct_0(B_1004)) | ~v1_funct_1(C_1005) | ~l1_pre_topc(B_1004) | ~v2_pre_topc(B_1004) | v2_struct_0(B_1004) | ~l1_pre_topc(A_1003) | ~v2_pre_topc(A_1003) | v2_struct_0(A_1003))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.27/2.45  tff(c_4742, plain, (![C_1005, D_1006]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), C_1005, u1_struct_0(D_1006))=k2_tmap_1('#skF_2', '#skF_3', C_1005, D_1006) | ~m1_pre_topc(D_1006, '#skF_2') | ~m1_subset_1(C_1005, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(C_1005, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_1005) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4272, c_4737])).
% 7.27/2.45  tff(c_4750, plain, (![C_1005, D_1006]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), C_1005, u1_struct_0(D_1006))=k2_tmap_1('#skF_2', '#skF_3', C_1005, D_1006) | ~m1_pre_topc(D_1006, '#skF_2') | ~m1_subset_1(C_1005, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(C_1005, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_1005) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_4742])).
% 7.27/2.45  tff(c_4751, plain, (![C_1005, D_1006]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), C_1005, u1_struct_0(D_1006))=k2_tmap_1('#skF_2', '#skF_3', C_1005, D_1006) | ~m1_pre_topc(D_1006, '#skF_2') | ~m1_subset_1(C_1005, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(C_1005, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_1005))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_4750])).
% 7.27/2.45  tff(c_5001, plain, (![E_1060]: (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', E_1060)=k2_tmap_1('#skF_2', '#skF_3', E_1060, '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(E_1060, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_1060, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_1060) | ~m1_subset_1(E_1060, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_1060, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_1060))), inference(superposition, [status(thm), theory('equality')], [c_4995, c_4751])).
% 7.27/2.45  tff(c_5015, plain, (![E_1061]: (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', E_1061)=k2_tmap_1('#skF_2', '#skF_3', E_1061, '#skF_4') | ~m1_subset_1(E_1061, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_1061, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_1061))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_5001])).
% 7.27/2.45  tff(c_5018, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4') | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_85, c_5015])).
% 7.27/2.45  tff(c_5021, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4268, c_5018])).
% 7.27/2.45  tff(c_4038, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_84])).
% 7.27/2.45  tff(c_5022, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5021, c_4038])).
% 7.27/2.45  tff(c_5024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4311, c_5022])).
% 7.27/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.27/2.45  
% 7.27/2.45  Inference rules
% 7.27/2.45  ----------------------
% 7.27/2.45  #Ref     : 0
% 7.27/2.45  #Sup     : 1039
% 7.27/2.45  #Fact    : 0
% 7.27/2.45  #Define  : 0
% 7.27/2.45  #Split   : 72
% 7.27/2.45  #Chain   : 0
% 7.27/2.45  #Close   : 0
% 7.27/2.45  
% 7.27/2.45  Ordering : KBO
% 7.27/2.45  
% 7.27/2.45  Simplification rules
% 7.27/2.45  ----------------------
% 7.27/2.45  #Subsume      : 290
% 7.27/2.45  #Demod        : 773
% 7.27/2.45  #Tautology    : 268
% 7.27/2.45  #SimpNegUnit  : 120
% 7.27/2.45  #BackRed      : 107
% 7.27/2.45  
% 7.27/2.45  #Partial instantiations: 0
% 7.27/2.45  #Strategies tried      : 1
% 7.27/2.45  
% 7.27/2.45  Timing (in seconds)
% 7.27/2.45  ----------------------
% 7.27/2.46  Preprocessing        : 0.39
% 7.27/2.46  Parsing              : 0.20
% 7.27/2.46  CNF conversion       : 0.05
% 7.27/2.46  Main loop            : 1.28
% 7.27/2.46  Inferencing          : 0.43
% 7.27/2.46  Reduction            : 0.39
% 7.27/2.46  Demodulation         : 0.27
% 7.27/2.46  BG Simplification    : 0.05
% 7.27/2.46  Subsumption          : 0.31
% 7.27/2.46  Abstraction          : 0.06
% 7.27/2.46  MUC search           : 0.00
% 7.27/2.46  Cooper               : 0.00
% 7.27/2.46  Total                : 1.73
% 7.27/2.46  Index Insertion      : 0.00
% 7.27/2.46  Index Deletion       : 0.00
% 7.27/2.46  Index Matching       : 0.00
% 7.27/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
