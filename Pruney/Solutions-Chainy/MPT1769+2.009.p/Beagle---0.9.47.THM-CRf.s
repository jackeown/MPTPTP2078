%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:19 EST 2020

% Result     : Theorem 9.37s
% Output     : CNFRefutation 9.69s
% Verified   : 
% Statistics : Number of formulae       :  188 (1739 expanded)
%              Number of leaves         :   38 ( 600 expanded)
%              Depth                    :   18
%              Number of atoms          :  634 (9822 expanded)
%              Number of equality atoms :   77 ( 669 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_206,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_78,axiom,(
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

tff(f_137,axiom,(
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

tff(f_105,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
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

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_34,plain,(
    '#skF_5' = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_86,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_202,plain,(
    ! [C_225,B_226,A_227] :
      ( v1_xboole_0(C_225)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(B_226,A_227)))
      | ~ v1_xboole_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_216,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_86,c_202])).

tff(c_220,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_50,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_40,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_38,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_85,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_32,plain,(
    r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_87,plain,(
    r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32])).

tff(c_1403,plain,(
    ! [F_441,B_440,E_443,D_442,A_439,C_438] :
      ( F_441 = E_443
      | ~ r1_funct_2(A_439,B_440,C_438,D_442,E_443,F_441)
      | ~ m1_subset_1(F_441,k1_zfmisc_1(k2_zfmisc_1(C_438,D_442)))
      | ~ v1_funct_2(F_441,C_438,D_442)
      | ~ v1_funct_1(F_441)
      | ~ m1_subset_1(E_443,k1_zfmisc_1(k2_zfmisc_1(A_439,B_440)))
      | ~ v1_funct_2(E_443,A_439,B_440)
      | ~ v1_funct_1(E_443)
      | v1_xboole_0(D_442)
      | v1_xboole_0(B_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1405,plain,
    ( '#skF_6' = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_87,c_1403])).

tff(c_1408,plain,
    ( '#skF_6' = '#skF_8'
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_40,c_85,c_86,c_1405])).

tff(c_1409,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_1408])).

tff(c_804,plain,(
    ! [C_334,E_339,F_337,D_338,B_336,A_335] :
      ( F_337 = E_339
      | ~ r1_funct_2(A_335,B_336,C_334,D_338,E_339,F_337)
      | ~ m1_subset_1(F_337,k1_zfmisc_1(k2_zfmisc_1(C_334,D_338)))
      | ~ v1_funct_2(F_337,C_334,D_338)
      | ~ v1_funct_1(F_337)
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(A_335,B_336)))
      | ~ v1_funct_2(E_339,A_335,B_336)
      | ~ v1_funct_1(E_339)
      | v1_xboole_0(D_338)
      | v1_xboole_0(B_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_808,plain,
    ( '#skF_6' = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_87,c_804])).

tff(c_816,plain,
    ( '#skF_6' = '#skF_8'
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_40,c_85,c_86,c_808])).

tff(c_817,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_816])).

tff(c_80,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_8'),'#skF_7')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_82,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_80])).

tff(c_244,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_820,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_244])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_83,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_54])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_1043,plain,(
    ! [C_364,A_363,E_366,D_367,B_365] :
      ( k3_tmap_1(A_363,B_365,C_364,D_367,E_366) = k2_partfun1(u1_struct_0(C_364),u1_struct_0(B_365),E_366,u1_struct_0(D_367))
      | ~ m1_pre_topc(D_367,C_364)
      | ~ m1_subset_1(E_366,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_364),u1_struct_0(B_365))))
      | ~ v1_funct_2(E_366,u1_struct_0(C_364),u1_struct_0(B_365))
      | ~ v1_funct_1(E_366)
      | ~ m1_pre_topc(D_367,A_363)
      | ~ m1_pre_topc(C_364,A_363)
      | ~ l1_pre_topc(B_365)
      | ~ v2_pre_topc(B_365)
      | v2_struct_0(B_365)
      | ~ l1_pre_topc(A_363)
      | ~ v2_pre_topc(A_363)
      | v2_struct_0(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1045,plain,(
    ! [A_363,D_367] :
      ( k3_tmap_1(A_363,'#skF_3','#skF_2',D_367,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_367))
      | ~ m1_pre_topc(D_367,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc(D_367,A_363)
      | ~ m1_pre_topc('#skF_2',A_363)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_363)
      | ~ v2_pre_topc(A_363)
      | v2_struct_0(A_363) ) ),
    inference(resolution,[status(thm)],[c_86,c_1043])).

tff(c_1053,plain,(
    ! [A_363,D_367] :
      ( k3_tmap_1(A_363,'#skF_3','#skF_2',D_367,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_367))
      | ~ m1_pre_topc(D_367,'#skF_2')
      | ~ m1_pre_topc(D_367,A_363)
      | ~ m1_pre_topc('#skF_2',A_363)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_363)
      | ~ v2_pre_topc(A_363)
      | v2_struct_0(A_363) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_40,c_85,c_1045])).

tff(c_1175,plain,(
    ! [A_396,D_397] :
      ( k3_tmap_1(A_396,'#skF_3','#skF_2',D_397,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_397))
      | ~ m1_pre_topc(D_397,'#skF_2')
      | ~ m1_pre_topc(D_397,A_396)
      | ~ m1_pre_topc('#skF_2',A_396)
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1053])).

tff(c_1177,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1175])).

tff(c_1182,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_83,c_58,c_1177])).

tff(c_1183,plain,(
    k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1182])).

tff(c_915,plain,(
    ! [A_352,B_353,C_354,D_355] :
      ( k2_partfun1(u1_struct_0(A_352),u1_struct_0(B_353),C_354,u1_struct_0(D_355)) = k2_tmap_1(A_352,B_353,C_354,D_355)
      | ~ m1_pre_topc(D_355,A_352)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_352),u1_struct_0(B_353))))
      | ~ v1_funct_2(C_354,u1_struct_0(A_352),u1_struct_0(B_353))
      | ~ v1_funct_1(C_354)
      | ~ l1_pre_topc(B_353)
      | ~ v2_pre_topc(B_353)
      | v2_struct_0(B_353)
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_917,plain,(
    ! [D_355] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_355)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_355)
      | ~ m1_pre_topc(D_355,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_86,c_915])).

tff(c_925,plain,(
    ! [D_355] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_355)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_355)
      | ~ m1_pre_topc(D_355,'#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_40,c_85,c_917])).

tff(c_926,plain,(
    ! [D_355] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_355)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_355)
      | ~ m1_pre_topc(D_355,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_925])).

tff(c_1191,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1183,c_926])).

tff(c_1198,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1191])).

tff(c_74,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7')
    | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_84,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7')
    | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_74])).

tff(c_308,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_84])).

tff(c_1203,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_308])).

tff(c_1206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_1203])).

tff(c_1208,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1411,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1409,c_1208])).

tff(c_1639,plain,(
    ! [A_487,C_488,E_490,B_489,D_491] :
      ( k3_tmap_1(A_487,B_489,C_488,D_491,E_490) = k2_partfun1(u1_struct_0(C_488),u1_struct_0(B_489),E_490,u1_struct_0(D_491))
      | ~ m1_pre_topc(D_491,C_488)
      | ~ m1_subset_1(E_490,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_488),u1_struct_0(B_489))))
      | ~ v1_funct_2(E_490,u1_struct_0(C_488),u1_struct_0(B_489))
      | ~ v1_funct_1(E_490)
      | ~ m1_pre_topc(D_491,A_487)
      | ~ m1_pre_topc(C_488,A_487)
      | ~ l1_pre_topc(B_489)
      | ~ v2_pre_topc(B_489)
      | v2_struct_0(B_489)
      | ~ l1_pre_topc(A_487)
      | ~ v2_pre_topc(A_487)
      | v2_struct_0(A_487) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1641,plain,(
    ! [A_487,D_491] :
      ( k3_tmap_1(A_487,'#skF_3','#skF_2',D_491,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_491))
      | ~ m1_pre_topc(D_491,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc(D_491,A_487)
      | ~ m1_pre_topc('#skF_2',A_487)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_487)
      | ~ v2_pre_topc(A_487)
      | v2_struct_0(A_487) ) ),
    inference(resolution,[status(thm)],[c_86,c_1639])).

tff(c_1649,plain,(
    ! [A_487,D_491] :
      ( k3_tmap_1(A_487,'#skF_3','#skF_2',D_491,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_491))
      | ~ m1_pre_topc(D_491,'#skF_2')
      | ~ m1_pre_topc(D_491,A_487)
      | ~ m1_pre_topc('#skF_2',A_487)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_487)
      | ~ v2_pre_topc(A_487)
      | v2_struct_0(A_487) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_40,c_85,c_1641])).

tff(c_1700,plain,(
    ! [A_503,D_504] :
      ( k3_tmap_1(A_503,'#skF_3','#skF_2',D_504,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_504))
      | ~ m1_pre_topc(D_504,'#skF_2')
      | ~ m1_pre_topc(D_504,A_503)
      | ~ m1_pre_topc('#skF_2',A_503)
      | ~ l1_pre_topc(A_503)
      | ~ v2_pre_topc(A_503)
      | v2_struct_0(A_503) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1649])).

tff(c_1702,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1700])).

tff(c_1707,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_83,c_58,c_1702])).

tff(c_1708,plain,(
    k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1707])).

tff(c_1608,plain,(
    ! [A_482,B_483,C_484,D_485] :
      ( k2_partfun1(u1_struct_0(A_482),u1_struct_0(B_483),C_484,u1_struct_0(D_485)) = k2_tmap_1(A_482,B_483,C_484,D_485)
      | ~ m1_pre_topc(D_485,A_482)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_482),u1_struct_0(B_483))))
      | ~ v1_funct_2(C_484,u1_struct_0(A_482),u1_struct_0(B_483))
      | ~ v1_funct_1(C_484)
      | ~ l1_pre_topc(B_483)
      | ~ v2_pre_topc(B_483)
      | v2_struct_0(B_483)
      | ~ l1_pre_topc(A_482)
      | ~ v2_pre_topc(A_482)
      | v2_struct_0(A_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1610,plain,(
    ! [D_485] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_485)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_485)
      | ~ m1_pre_topc(D_485,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_86,c_1608])).

tff(c_1618,plain,(
    ! [D_485] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_485)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_485)
      | ~ m1_pre_topc(D_485,'#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_40,c_85,c_1610])).

tff(c_1619,plain,(
    ! [D_485] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_485)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_485)
      | ~ m1_pre_topc(D_485,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_1618])).

tff(c_1716,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1708,c_1619])).

tff(c_1723,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1716])).

tff(c_1207,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1728,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1723,c_1207])).

tff(c_1730,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1411,c_1728])).

tff(c_1731,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1869,plain,(
    ! [A_509,A_510,B_511] :
      ( v1_xboole_0(A_509)
      | ~ v1_xboole_0(A_510)
      | ~ r1_tarski(A_509,k2_zfmisc_1(B_511,A_510)) ) ),
    inference(resolution,[status(thm)],[c_16,c_202])).

tff(c_1899,plain,(
    ! [B_513,A_514] :
      ( v1_xboole_0(k2_zfmisc_1(B_513,A_514))
      | ~ v1_xboole_0(A_514) ) ),
    inference(resolution,[status(thm)],[c_12,c_1869])).

tff(c_1732,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,(
    ! [C_207,B_208,A_209] :
      ( ~ v1_xboole_0(C_207)
      | ~ m1_subset_1(B_208,k1_zfmisc_1(C_207))
      | ~ r2_hidden(A_209,B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_150,plain,(
    ! [B_210,A_211,A_212] :
      ( ~ v1_xboole_0(B_210)
      | ~ r2_hidden(A_211,A_212)
      | ~ r1_tarski(A_212,B_210) ) ),
    inference(resolution,[status(thm)],[c_16,c_136])).

tff(c_154,plain,(
    ! [B_213,A_214,B_215] :
      ( ~ v1_xboole_0(B_213)
      | ~ r1_tarski(A_214,B_213)
      | r1_tarski(A_214,B_215) ) ),
    inference(resolution,[status(thm)],[c_6,c_150])).

tff(c_166,plain,(
    ! [B_7,B_215] :
      ( ~ v1_xboole_0(B_7)
      | r1_tarski(B_7,B_215) ) ),
    inference(resolution,[status(thm)],[c_12,c_154])).

tff(c_167,plain,(
    ! [B_216,B_217] :
      ( ~ v1_xboole_0(B_216)
      | r1_tarski(B_216,B_217) ) ),
    inference(resolution,[status(thm)],[c_12,c_154])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_174,plain,(
    ! [B_219,B_218] :
      ( B_219 = B_218
      | ~ r1_tarski(B_218,B_219)
      | ~ v1_xboole_0(B_219) ) ),
    inference(resolution,[status(thm)],[c_167,c_8])).

tff(c_190,plain,(
    ! [B_7,B_215] :
      ( B_7 = B_215
      | ~ v1_xboole_0(B_215)
      | ~ v1_xboole_0(B_7) ) ),
    inference(resolution,[status(thm)],[c_166,c_174])).

tff(c_1739,plain,(
    ! [B_505] :
      ( B_505 = '#skF_8'
      | ~ v1_xboole_0(B_505) ) ),
    inference(resolution,[status(thm)],[c_1731,c_190])).

tff(c_1746,plain,(
    u1_struct_0('#skF_3') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1732,c_1739])).

tff(c_145,plain,(
    ! [A_209] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_209,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_86,c_136])).

tff(c_201,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_1751,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1746,c_201])).

tff(c_1902,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1899,c_1751])).

tff(c_1914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1731,c_1902])).

tff(c_1916,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_1917,plain,(
    ! [A_515] : ~ r2_hidden(A_515,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_1924,plain,(
    ! [B_516] : r1_tarski('#skF_8',B_516) ),
    inference(resolution,[status(thm)],[c_6,c_1917])).

tff(c_173,plain,(
    ! [B_217,B_216] :
      ( B_217 = B_216
      | ~ r1_tarski(B_217,B_216)
      | ~ v1_xboole_0(B_216) ) ),
    inference(resolution,[status(thm)],[c_167,c_8])).

tff(c_1932,plain,(
    ! [B_516] :
      ( B_516 = '#skF_8'
      | ~ v1_xboole_0(B_516) ) ),
    inference(resolution,[status(thm)],[c_1924,c_173])).

tff(c_1979,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1916,c_1932])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_125,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_48,c_14])).

tff(c_1982,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1979,c_125])).

tff(c_1935,plain,(
    ! [B_516] :
      ( B_516 = '#skF_8'
      | ~ r1_tarski(B_516,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1924,c_8])).

tff(c_2010,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1982,c_1935])).

tff(c_2208,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_82])).

tff(c_2209,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2208])).

tff(c_1984,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1979,c_48])).

tff(c_2034,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_1984])).

tff(c_2696,plain,(
    ! [A_604,B_605,C_606,D_607] :
      ( k2_partfun1(u1_struct_0(A_604),u1_struct_0(B_605),C_606,u1_struct_0(D_607)) = k2_tmap_1(A_604,B_605,C_606,D_607)
      | ~ m1_pre_topc(D_607,A_604)
      | ~ m1_subset_1(C_606,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_604),u1_struct_0(B_605))))
      | ~ v1_funct_2(C_606,u1_struct_0(A_604),u1_struct_0(B_605))
      | ~ v1_funct_1(C_606)
      | ~ l1_pre_topc(B_605)
      | ~ v2_pre_topc(B_605)
      | v2_struct_0(B_605)
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_5073,plain,(
    ! [A_722,B_723,A_724,D_725] :
      ( k2_partfun1(u1_struct_0(A_722),u1_struct_0(B_723),A_724,u1_struct_0(D_725)) = k2_tmap_1(A_722,B_723,A_724,D_725)
      | ~ m1_pre_topc(D_725,A_722)
      | ~ v1_funct_2(A_724,u1_struct_0(A_722),u1_struct_0(B_723))
      | ~ v1_funct_1(A_724)
      | ~ l1_pre_topc(B_723)
      | ~ v2_pre_topc(B_723)
      | v2_struct_0(B_723)
      | ~ l1_pre_topc(A_722)
      | ~ v2_pre_topc(A_722)
      | v2_struct_0(A_722)
      | ~ r1_tarski(A_724,k2_zfmisc_1(u1_struct_0(A_722),u1_struct_0(B_723))) ) ),
    inference(resolution,[status(thm)],[c_16,c_2696])).

tff(c_7122,plain,(
    ! [A_797,B_798,D_799] :
      ( k2_partfun1(u1_struct_0(A_797),u1_struct_0(B_798),k2_zfmisc_1(u1_struct_0(A_797),u1_struct_0(B_798)),u1_struct_0(D_799)) = k2_tmap_1(A_797,B_798,k2_zfmisc_1(u1_struct_0(A_797),u1_struct_0(B_798)),D_799)
      | ~ m1_pre_topc(D_799,A_797)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_797),u1_struct_0(B_798)),u1_struct_0(A_797),u1_struct_0(B_798))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_797),u1_struct_0(B_798)))
      | ~ l1_pre_topc(B_798)
      | ~ v2_pre_topc(B_798)
      | v2_struct_0(B_798)
      | ~ l1_pre_topc(A_797)
      | ~ v2_pre_topc(A_797)
      | v2_struct_0(A_797) ) ),
    inference(resolution,[status(thm)],[c_12,c_5073])).

tff(c_3082,plain,(
    ! [A_621,C_622,B_623,E_624,D_625] :
      ( k3_tmap_1(A_621,B_623,C_622,D_625,E_624) = k2_partfun1(u1_struct_0(C_622),u1_struct_0(B_623),E_624,u1_struct_0(D_625))
      | ~ m1_pre_topc(D_625,C_622)
      | ~ m1_subset_1(E_624,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_622),u1_struct_0(B_623))))
      | ~ v1_funct_2(E_624,u1_struct_0(C_622),u1_struct_0(B_623))
      | ~ v1_funct_1(E_624)
      | ~ m1_pre_topc(D_625,A_621)
      | ~ m1_pre_topc(C_622,A_621)
      | ~ l1_pre_topc(B_623)
      | ~ v2_pre_topc(B_623)
      | v2_struct_0(B_623)
      | ~ l1_pre_topc(A_621)
      | ~ v2_pre_topc(A_621)
      | v2_struct_0(A_621) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_3084,plain,(
    ! [A_621,D_625,E_624] :
      ( k3_tmap_1(A_621,'#skF_3','#skF_2',D_625,E_624) = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_624,u1_struct_0(D_625))
      | ~ m1_pre_topc(D_625,'#skF_2')
      | ~ m1_subset_1(E_624,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_624,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_624)
      | ~ m1_pre_topc(D_625,A_621)
      | ~ m1_pre_topc('#skF_2',A_621)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_621)
      | ~ v2_pre_topc(A_621)
      | v2_struct_0(A_621) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1979,c_3082])).

tff(c_3091,plain,(
    ! [A_621,D_625,E_624] :
      ( k3_tmap_1(A_621,'#skF_3','#skF_2',D_625,E_624) = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_624,u1_struct_0(D_625))
      | ~ m1_pre_topc(D_625,'#skF_2')
      | ~ m1_subset_1(E_624,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_624,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_624)
      | ~ m1_pre_topc(D_625,A_621)
      | ~ m1_pre_topc('#skF_2',A_621)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_621)
      | ~ v2_pre_topc(A_621)
      | v2_struct_0(A_621) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_3084])).

tff(c_3865,plain,(
    ! [A_669,D_670,E_671] :
      ( k3_tmap_1(A_669,'#skF_3','#skF_2',D_670,E_671) = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_671,u1_struct_0(D_670))
      | ~ m1_pre_topc(D_670,'#skF_2')
      | ~ m1_subset_1(E_671,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_671,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_671)
      | ~ m1_pre_topc(D_670,A_669)
      | ~ m1_pre_topc('#skF_2',A_669)
      | ~ l1_pre_topc(A_669)
      | ~ v2_pre_topc(A_669)
      | v2_struct_0(A_669) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3091])).

tff(c_3867,plain,(
    ! [E_671] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_671,u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',E_671)
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | ~ m1_subset_1(E_671,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_671,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_671)
      | ~ m1_pre_topc('#skF_2','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_3865])).

tff(c_3872,plain,(
    ! [E_671] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_671,u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',E_671)
      | ~ m1_subset_1(E_671,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_671,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_671)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_83,c_58,c_3867])).

tff(c_3873,plain,(
    ! [E_671] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_671,u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',E_671)
      | ~ m1_subset_1(E_671,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_2(E_671,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_671) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3872])).

tff(c_7137,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) = k2_tmap_1('#skF_2','#skF_3',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')),'#skF_4')
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')),k1_zfmisc_1('#skF_8'))
    | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7122,c_3873])).

tff(c_7180,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_40,c_1979,c_85,c_1979,c_58,c_40,c_1979,c_85,c_1979,c_2034,c_1979,c_1979,c_1979,c_7137])).

tff(c_7181,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_7180])).

tff(c_2250,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7')
    | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_84])).

tff(c_2251,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2250])).

tff(c_7212,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7181,c_2251])).

tff(c_7215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2209,c_7212])).

tff(c_7216,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_2250])).

tff(c_7234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2209,c_7216])).

tff(c_7235,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_2208])).

tff(c_7262,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7')
    | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_84])).

tff(c_7263,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_7262])).

tff(c_7297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7235,c_7263])).

tff(c_7298,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_7262])).

tff(c_1922,plain,(
    ! [B_2] : r1_tarski('#skF_8',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_1917])).

tff(c_7613,plain,(
    ! [A_857,B_858,C_859,D_860] :
      ( k2_partfun1(u1_struct_0(A_857),u1_struct_0(B_858),C_859,u1_struct_0(D_860)) = k2_tmap_1(A_857,B_858,C_859,D_860)
      | ~ m1_pre_topc(D_860,A_857)
      | ~ m1_subset_1(C_859,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_857),u1_struct_0(B_858))))
      | ~ v1_funct_2(C_859,u1_struct_0(A_857),u1_struct_0(B_858))
      | ~ v1_funct_1(C_859)
      | ~ l1_pre_topc(B_858)
      | ~ v2_pre_topc(B_858)
      | v2_struct_0(B_858)
      | ~ l1_pre_topc(A_857)
      | ~ v2_pre_topc(A_857)
      | v2_struct_0(A_857) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_9593,plain,(
    ! [A_982,B_983,A_984,D_985] :
      ( k2_partfun1(u1_struct_0(A_982),u1_struct_0(B_983),A_984,u1_struct_0(D_985)) = k2_tmap_1(A_982,B_983,A_984,D_985)
      | ~ m1_pre_topc(D_985,A_982)
      | ~ v1_funct_2(A_984,u1_struct_0(A_982),u1_struct_0(B_983))
      | ~ v1_funct_1(A_984)
      | ~ l1_pre_topc(B_983)
      | ~ v2_pre_topc(B_983)
      | v2_struct_0(B_983)
      | ~ l1_pre_topc(A_982)
      | ~ v2_pre_topc(A_982)
      | v2_struct_0(A_982)
      | ~ r1_tarski(A_984,k2_zfmisc_1(u1_struct_0(A_982),u1_struct_0(B_983))) ) ),
    inference(resolution,[status(thm)],[c_16,c_7613])).

tff(c_13127,plain,(
    ! [A_1076,B_1077,D_1078] :
      ( k2_partfun1(u1_struct_0(A_1076),u1_struct_0(B_1077),k2_zfmisc_1(u1_struct_0(A_1076),u1_struct_0(B_1077)),u1_struct_0(D_1078)) = k2_tmap_1(A_1076,B_1077,k2_zfmisc_1(u1_struct_0(A_1076),u1_struct_0(B_1077)),D_1078)
      | ~ m1_pre_topc(D_1078,A_1076)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_1076),u1_struct_0(B_1077)),u1_struct_0(A_1076),u1_struct_0(B_1077))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_1076),u1_struct_0(B_1077)))
      | ~ l1_pre_topc(B_1077)
      | ~ v2_pre_topc(B_1077)
      | v2_struct_0(B_1077)
      | ~ l1_pre_topc(A_1076)
      | ~ v2_pre_topc(A_1076)
      | v2_struct_0(A_1076) ) ),
    inference(resolution,[status(thm)],[c_12,c_9593])).

tff(c_7793,plain,(
    ! [C_878,E_880,B_879,A_877,D_881] :
      ( k3_tmap_1(A_877,B_879,C_878,D_881,E_880) = k2_partfun1(u1_struct_0(C_878),u1_struct_0(B_879),E_880,u1_struct_0(D_881))
      | ~ m1_pre_topc(D_881,C_878)
      | ~ m1_subset_1(E_880,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_878),u1_struct_0(B_879))))
      | ~ v1_funct_2(E_880,u1_struct_0(C_878),u1_struct_0(B_879))
      | ~ v1_funct_1(E_880)
      | ~ m1_pre_topc(D_881,A_877)
      | ~ m1_pre_topc(C_878,A_877)
      | ~ l1_pre_topc(B_879)
      | ~ v2_pre_topc(B_879)
      | v2_struct_0(B_879)
      | ~ l1_pre_topc(A_877)
      | ~ v2_pre_topc(A_877)
      | v2_struct_0(A_877) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_10843,plain,(
    ! [A_1008,B_1006,C_1005,D_1004,A_1007] :
      ( k3_tmap_1(A_1008,B_1006,C_1005,D_1004,A_1007) = k2_partfun1(u1_struct_0(C_1005),u1_struct_0(B_1006),A_1007,u1_struct_0(D_1004))
      | ~ m1_pre_topc(D_1004,C_1005)
      | ~ v1_funct_2(A_1007,u1_struct_0(C_1005),u1_struct_0(B_1006))
      | ~ v1_funct_1(A_1007)
      | ~ m1_pre_topc(D_1004,A_1008)
      | ~ m1_pre_topc(C_1005,A_1008)
      | ~ l1_pre_topc(B_1006)
      | ~ v2_pre_topc(B_1006)
      | v2_struct_0(B_1006)
      | ~ l1_pre_topc(A_1008)
      | ~ v2_pre_topc(A_1008)
      | v2_struct_0(A_1008)
      | ~ r1_tarski(A_1007,k2_zfmisc_1(u1_struct_0(C_1005),u1_struct_0(B_1006))) ) ),
    inference(resolution,[status(thm)],[c_16,c_7793])).

tff(c_10845,plain,(
    ! [C_1005,B_1006,A_1007] :
      ( k2_partfun1(u1_struct_0(C_1005),u1_struct_0(B_1006),A_1007,u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2',B_1006,C_1005,'#skF_4',A_1007)
      | ~ m1_pre_topc('#skF_4',C_1005)
      | ~ v1_funct_2(A_1007,u1_struct_0(C_1005),u1_struct_0(B_1006))
      | ~ v1_funct_1(A_1007)
      | ~ m1_pre_topc(C_1005,'#skF_2')
      | ~ l1_pre_topc(B_1006)
      | ~ v2_pre_topc(B_1006)
      | v2_struct_0(B_1006)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_1007,k2_zfmisc_1(u1_struct_0(C_1005),u1_struct_0(B_1006))) ) ),
    inference(resolution,[status(thm)],[c_58,c_10843])).

tff(c_10850,plain,(
    ! [C_1005,B_1006,A_1007] :
      ( k2_partfun1(u1_struct_0(C_1005),u1_struct_0(B_1006),A_1007,u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2',B_1006,C_1005,'#skF_4',A_1007)
      | ~ m1_pre_topc('#skF_4',C_1005)
      | ~ v1_funct_2(A_1007,u1_struct_0(C_1005),u1_struct_0(B_1006))
      | ~ v1_funct_1(A_1007)
      | ~ m1_pre_topc(C_1005,'#skF_2')
      | ~ l1_pre_topc(B_1006)
      | ~ v2_pre_topc(B_1006)
      | v2_struct_0(B_1006)
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_1007,k2_zfmisc_1(u1_struct_0(C_1005),u1_struct_0(B_1006))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_10845])).

tff(c_11784,plain,(
    ! [C_1041,B_1042,A_1043] :
      ( k2_partfun1(u1_struct_0(C_1041),u1_struct_0(B_1042),A_1043,u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2',B_1042,C_1041,'#skF_4',A_1043)
      | ~ m1_pre_topc('#skF_4',C_1041)
      | ~ v1_funct_2(A_1043,u1_struct_0(C_1041),u1_struct_0(B_1042))
      | ~ v1_funct_1(A_1043)
      | ~ m1_pre_topc(C_1041,'#skF_2')
      | ~ l1_pre_topc(B_1042)
      | ~ v2_pre_topc(B_1042)
      | v2_struct_0(B_1042)
      | ~ r1_tarski(A_1043,k2_zfmisc_1(u1_struct_0(C_1041),u1_struct_0(B_1042))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_10850])).

tff(c_11790,plain,(
    ! [A_1043] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),A_1043,u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',A_1043)
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | ~ v1_funct_2(A_1043,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(A_1043)
      | ~ m1_pre_topc('#skF_2','#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_1043,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1979,c_11784])).

tff(c_11811,plain,(
    ! [A_1043] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),A_1043,u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',A_1043)
      | ~ v1_funct_2(A_1043,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(A_1043)
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_1043,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_83,c_58,c_11790])).

tff(c_11812,plain,(
    ! [A_1043] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),A_1043,u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',A_1043)
      | ~ v1_funct_2(A_1043,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(A_1043)
      | ~ r1_tarski(A_1043,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_11811])).

tff(c_13138,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) = k2_tmap_1('#skF_2','#skF_3',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')),'#skF_4')
    | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')),'#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13127,c_11812])).

tff(c_13190,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_40,c_1979,c_85,c_1979,c_58,c_1922,c_1979,c_40,c_1979,c_85,c_1979,c_1979,c_1979,c_13138])).

tff(c_13191,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_13190])).

tff(c_7299,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_7262])).

tff(c_13230,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13191,c_7299])).

tff(c_13232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7298,c_13230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:07:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.37/3.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.37/3.30  
% 9.37/3.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.37/3.30  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 9.37/3.30  
% 9.37/3.30  %Foreground sorts:
% 9.37/3.30  
% 9.37/3.30  
% 9.37/3.30  %Background operators:
% 9.37/3.30  
% 9.37/3.30  
% 9.37/3.30  %Foreground operators:
% 9.37/3.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.37/3.30  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 9.37/3.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.37/3.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.37/3.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.37/3.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.37/3.30  tff('#skF_7', type, '#skF_7': $i).
% 9.37/3.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.37/3.30  tff('#skF_5', type, '#skF_5': $i).
% 9.37/3.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.37/3.30  tff('#skF_6', type, '#skF_6': $i).
% 9.37/3.30  tff('#skF_2', type, '#skF_2': $i).
% 9.37/3.30  tff('#skF_3', type, '#skF_3': $i).
% 9.37/3.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.37/3.30  tff('#skF_8', type, '#skF_8': $i).
% 9.37/3.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.37/3.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.37/3.30  tff('#skF_4', type, '#skF_4': $i).
% 9.37/3.30  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 9.37/3.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.37/3.30  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.37/3.30  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.37/3.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.37/3.30  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 9.37/3.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.37/3.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.37/3.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.37/3.30  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 9.37/3.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.37/3.30  
% 9.69/3.33  tff(f_206, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_tmap_1)).
% 9.69/3.33  tff(f_56, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 9.69/3.33  tff(f_78, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 9.69/3.33  tff(f_137, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 9.69/3.33  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 9.69/3.33  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.69/3.33  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.69/3.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.69/3.33  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 9.69/3.33  tff(c_34, plain, ('#skF_5'='#skF_2'), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_36, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_86, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 9.69/3.33  tff(c_202, plain, (![C_225, B_226, A_227]: (v1_xboole_0(C_225) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(B_226, A_227))) | ~v1_xboole_0(A_227))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.69/3.33  tff(c_216, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_86, c_202])).
% 9.69/3.33  tff(c_220, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_216])).
% 9.69/3.33  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_50, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_40, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_38, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_85, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 9.69/3.33  tff(c_32, plain, (r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_87, plain, (r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32])).
% 9.69/3.33  tff(c_1403, plain, (![F_441, B_440, E_443, D_442, A_439, C_438]: (F_441=E_443 | ~r1_funct_2(A_439, B_440, C_438, D_442, E_443, F_441) | ~m1_subset_1(F_441, k1_zfmisc_1(k2_zfmisc_1(C_438, D_442))) | ~v1_funct_2(F_441, C_438, D_442) | ~v1_funct_1(F_441) | ~m1_subset_1(E_443, k1_zfmisc_1(k2_zfmisc_1(A_439, B_440))) | ~v1_funct_2(E_443, A_439, B_440) | ~v1_funct_1(E_443) | v1_xboole_0(D_442) | v1_xboole_0(B_440))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.69/3.33  tff(c_1405, plain, ('#skF_6'='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_87, c_1403])).
% 9.69/3.33  tff(c_1408, plain, ('#skF_6'='#skF_8' | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_40, c_85, c_86, c_1405])).
% 9.69/3.33  tff(c_1409, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_220, c_1408])).
% 9.69/3.33  tff(c_804, plain, (![C_334, E_339, F_337, D_338, B_336, A_335]: (F_337=E_339 | ~r1_funct_2(A_335, B_336, C_334, D_338, E_339, F_337) | ~m1_subset_1(F_337, k1_zfmisc_1(k2_zfmisc_1(C_334, D_338))) | ~v1_funct_2(F_337, C_334, D_338) | ~v1_funct_1(F_337) | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(A_335, B_336))) | ~v1_funct_2(E_339, A_335, B_336) | ~v1_funct_1(E_339) | v1_xboole_0(D_338) | v1_xboole_0(B_336))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.69/3.33  tff(c_808, plain, ('#skF_6'='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_87, c_804])).
% 9.69/3.33  tff(c_816, plain, ('#skF_6'='#skF_8' | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_40, c_85, c_86, c_808])).
% 9.69/3.33  tff(c_817, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_220, c_816])).
% 9.69/3.33  tff(c_80, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_8'), '#skF_7') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_82, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_80])).
% 9.69/3.33  tff(c_244, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(splitLeft, [status(thm)], [c_82])).
% 9.69/3.33  tff(c_820, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_817, c_244])).
% 9.69/3.33  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_83, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_54])).
% 9.69/3.33  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_1043, plain, (![C_364, A_363, E_366, D_367, B_365]: (k3_tmap_1(A_363, B_365, C_364, D_367, E_366)=k2_partfun1(u1_struct_0(C_364), u1_struct_0(B_365), E_366, u1_struct_0(D_367)) | ~m1_pre_topc(D_367, C_364) | ~m1_subset_1(E_366, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_364), u1_struct_0(B_365)))) | ~v1_funct_2(E_366, u1_struct_0(C_364), u1_struct_0(B_365)) | ~v1_funct_1(E_366) | ~m1_pre_topc(D_367, A_363) | ~m1_pre_topc(C_364, A_363) | ~l1_pre_topc(B_365) | ~v2_pre_topc(B_365) | v2_struct_0(B_365) | ~l1_pre_topc(A_363) | ~v2_pre_topc(A_363) | v2_struct_0(A_363))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.69/3.33  tff(c_1045, plain, (![A_363, D_367]: (k3_tmap_1(A_363, '#skF_3', '#skF_2', D_367, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_367)) | ~m1_pre_topc(D_367, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc(D_367, A_363) | ~m1_pre_topc('#skF_2', A_363) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_363) | ~v2_pre_topc(A_363) | v2_struct_0(A_363))), inference(resolution, [status(thm)], [c_86, c_1043])).
% 9.69/3.33  tff(c_1053, plain, (![A_363, D_367]: (k3_tmap_1(A_363, '#skF_3', '#skF_2', D_367, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_367)) | ~m1_pre_topc(D_367, '#skF_2') | ~m1_pre_topc(D_367, A_363) | ~m1_pre_topc('#skF_2', A_363) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_363) | ~v2_pre_topc(A_363) | v2_struct_0(A_363))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_40, c_85, c_1045])).
% 9.69/3.33  tff(c_1175, plain, (![A_396, D_397]: (k3_tmap_1(A_396, '#skF_3', '#skF_2', D_397, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_397)) | ~m1_pre_topc(D_397, '#skF_2') | ~m1_pre_topc(D_397, A_396) | ~m1_pre_topc('#skF_2', A_396) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396))), inference(negUnitSimplification, [status(thm)], [c_66, c_1053])).
% 9.69/3.33  tff(c_1177, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_1175])).
% 9.69/3.33  tff(c_1182, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_83, c_58, c_1177])).
% 9.69/3.33  tff(c_1183, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_72, c_1182])).
% 9.69/3.33  tff(c_915, plain, (![A_352, B_353, C_354, D_355]: (k2_partfun1(u1_struct_0(A_352), u1_struct_0(B_353), C_354, u1_struct_0(D_355))=k2_tmap_1(A_352, B_353, C_354, D_355) | ~m1_pre_topc(D_355, A_352) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_352), u1_struct_0(B_353)))) | ~v1_funct_2(C_354, u1_struct_0(A_352), u1_struct_0(B_353)) | ~v1_funct_1(C_354) | ~l1_pre_topc(B_353) | ~v2_pre_topc(B_353) | v2_struct_0(B_353) | ~l1_pre_topc(A_352) | ~v2_pre_topc(A_352) | v2_struct_0(A_352))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.69/3.33  tff(c_917, plain, (![D_355]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_355))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_355) | ~m1_pre_topc(D_355, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_86, c_915])).
% 9.69/3.33  tff(c_925, plain, (![D_355]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_355))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_355) | ~m1_pre_topc(D_355, '#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_40, c_85, c_917])).
% 9.69/3.33  tff(c_926, plain, (![D_355]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_355))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_355) | ~m1_pre_topc(D_355, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_925])).
% 9.69/3.33  tff(c_1191, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1183, c_926])).
% 9.69/3.33  tff(c_1198, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1191])).
% 9.69/3.33  tff(c_74, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.69/3.33  tff(c_84, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_74])).
% 9.69/3.33  tff(c_308, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_84])).
% 9.69/3.33  tff(c_1203, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_308])).
% 9.69/3.33  tff(c_1206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_820, c_1203])).
% 9.69/3.33  tff(c_1208, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(splitRight, [status(thm)], [c_82])).
% 9.69/3.33  tff(c_1411, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1409, c_1208])).
% 9.69/3.33  tff(c_1639, plain, (![A_487, C_488, E_490, B_489, D_491]: (k3_tmap_1(A_487, B_489, C_488, D_491, E_490)=k2_partfun1(u1_struct_0(C_488), u1_struct_0(B_489), E_490, u1_struct_0(D_491)) | ~m1_pre_topc(D_491, C_488) | ~m1_subset_1(E_490, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_488), u1_struct_0(B_489)))) | ~v1_funct_2(E_490, u1_struct_0(C_488), u1_struct_0(B_489)) | ~v1_funct_1(E_490) | ~m1_pre_topc(D_491, A_487) | ~m1_pre_topc(C_488, A_487) | ~l1_pre_topc(B_489) | ~v2_pre_topc(B_489) | v2_struct_0(B_489) | ~l1_pre_topc(A_487) | ~v2_pre_topc(A_487) | v2_struct_0(A_487))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.69/3.33  tff(c_1641, plain, (![A_487, D_491]: (k3_tmap_1(A_487, '#skF_3', '#skF_2', D_491, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_491)) | ~m1_pre_topc(D_491, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc(D_491, A_487) | ~m1_pre_topc('#skF_2', A_487) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_487) | ~v2_pre_topc(A_487) | v2_struct_0(A_487))), inference(resolution, [status(thm)], [c_86, c_1639])).
% 9.69/3.33  tff(c_1649, plain, (![A_487, D_491]: (k3_tmap_1(A_487, '#skF_3', '#skF_2', D_491, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_491)) | ~m1_pre_topc(D_491, '#skF_2') | ~m1_pre_topc(D_491, A_487) | ~m1_pre_topc('#skF_2', A_487) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_487) | ~v2_pre_topc(A_487) | v2_struct_0(A_487))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_40, c_85, c_1641])).
% 9.69/3.33  tff(c_1700, plain, (![A_503, D_504]: (k3_tmap_1(A_503, '#skF_3', '#skF_2', D_504, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_504)) | ~m1_pre_topc(D_504, '#skF_2') | ~m1_pre_topc(D_504, A_503) | ~m1_pre_topc('#skF_2', A_503) | ~l1_pre_topc(A_503) | ~v2_pre_topc(A_503) | v2_struct_0(A_503))), inference(negUnitSimplification, [status(thm)], [c_66, c_1649])).
% 9.69/3.33  tff(c_1702, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_1700])).
% 9.69/3.33  tff(c_1707, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_83, c_58, c_1702])).
% 9.69/3.33  tff(c_1708, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_72, c_1707])).
% 9.69/3.33  tff(c_1608, plain, (![A_482, B_483, C_484, D_485]: (k2_partfun1(u1_struct_0(A_482), u1_struct_0(B_483), C_484, u1_struct_0(D_485))=k2_tmap_1(A_482, B_483, C_484, D_485) | ~m1_pre_topc(D_485, A_482) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_482), u1_struct_0(B_483)))) | ~v1_funct_2(C_484, u1_struct_0(A_482), u1_struct_0(B_483)) | ~v1_funct_1(C_484) | ~l1_pre_topc(B_483) | ~v2_pre_topc(B_483) | v2_struct_0(B_483) | ~l1_pre_topc(A_482) | ~v2_pre_topc(A_482) | v2_struct_0(A_482))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.69/3.33  tff(c_1610, plain, (![D_485]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_485))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_485) | ~m1_pre_topc(D_485, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_86, c_1608])).
% 9.69/3.33  tff(c_1618, plain, (![D_485]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_485))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_485) | ~m1_pre_topc(D_485, '#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_40, c_85, c_1610])).
% 9.69/3.33  tff(c_1619, plain, (![D_485]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_485))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_485) | ~m1_pre_topc(D_485, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_1618])).
% 9.69/3.33  tff(c_1716, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1708, c_1619])).
% 9.69/3.33  tff(c_1723, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1716])).
% 9.69/3.33  tff(c_1207, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_82])).
% 9.69/3.33  tff(c_1728, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1723, c_1207])).
% 9.69/3.33  tff(c_1730, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1411, c_1728])).
% 9.69/3.33  tff(c_1731, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_216])).
% 9.69/3.33  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.69/3.33  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.69/3.33  tff(c_1869, plain, (![A_509, A_510, B_511]: (v1_xboole_0(A_509) | ~v1_xboole_0(A_510) | ~r1_tarski(A_509, k2_zfmisc_1(B_511, A_510)))), inference(resolution, [status(thm)], [c_16, c_202])).
% 9.69/3.33  tff(c_1899, plain, (![B_513, A_514]: (v1_xboole_0(k2_zfmisc_1(B_513, A_514)) | ~v1_xboole_0(A_514))), inference(resolution, [status(thm)], [c_12, c_1869])).
% 9.69/3.33  tff(c_1732, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_216])).
% 9.69/3.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.69/3.33  tff(c_136, plain, (![C_207, B_208, A_209]: (~v1_xboole_0(C_207) | ~m1_subset_1(B_208, k1_zfmisc_1(C_207)) | ~r2_hidden(A_209, B_208))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.69/3.33  tff(c_150, plain, (![B_210, A_211, A_212]: (~v1_xboole_0(B_210) | ~r2_hidden(A_211, A_212) | ~r1_tarski(A_212, B_210))), inference(resolution, [status(thm)], [c_16, c_136])).
% 9.69/3.33  tff(c_154, plain, (![B_213, A_214, B_215]: (~v1_xboole_0(B_213) | ~r1_tarski(A_214, B_213) | r1_tarski(A_214, B_215))), inference(resolution, [status(thm)], [c_6, c_150])).
% 9.69/3.33  tff(c_166, plain, (![B_7, B_215]: (~v1_xboole_0(B_7) | r1_tarski(B_7, B_215))), inference(resolution, [status(thm)], [c_12, c_154])).
% 9.69/3.33  tff(c_167, plain, (![B_216, B_217]: (~v1_xboole_0(B_216) | r1_tarski(B_216, B_217))), inference(resolution, [status(thm)], [c_12, c_154])).
% 9.69/3.33  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.69/3.33  tff(c_174, plain, (![B_219, B_218]: (B_219=B_218 | ~r1_tarski(B_218, B_219) | ~v1_xboole_0(B_219))), inference(resolution, [status(thm)], [c_167, c_8])).
% 9.69/3.33  tff(c_190, plain, (![B_7, B_215]: (B_7=B_215 | ~v1_xboole_0(B_215) | ~v1_xboole_0(B_7))), inference(resolution, [status(thm)], [c_166, c_174])).
% 9.69/3.33  tff(c_1739, plain, (![B_505]: (B_505='#skF_8' | ~v1_xboole_0(B_505))), inference(resolution, [status(thm)], [c_1731, c_190])).
% 9.69/3.33  tff(c_1746, plain, (u1_struct_0('#skF_3')='#skF_8'), inference(resolution, [status(thm)], [c_1732, c_1739])).
% 9.69/3.33  tff(c_145, plain, (![A_209]: (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~r2_hidden(A_209, '#skF_8'))), inference(resolution, [status(thm)], [c_86, c_136])).
% 9.69/3.33  tff(c_201, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_145])).
% 9.69/3.33  tff(c_1751, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1746, c_201])).
% 9.69/3.33  tff(c_1902, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_1899, c_1751])).
% 9.69/3.33  tff(c_1914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1731, c_1902])).
% 9.69/3.33  tff(c_1916, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_145])).
% 9.69/3.33  tff(c_1917, plain, (![A_515]: (~r2_hidden(A_515, '#skF_8'))), inference(splitRight, [status(thm)], [c_145])).
% 9.69/3.33  tff(c_1924, plain, (![B_516]: (r1_tarski('#skF_8', B_516))), inference(resolution, [status(thm)], [c_6, c_1917])).
% 9.69/3.33  tff(c_173, plain, (![B_217, B_216]: (B_217=B_216 | ~r1_tarski(B_217, B_216) | ~v1_xboole_0(B_216))), inference(resolution, [status(thm)], [c_167, c_8])).
% 9.69/3.33  tff(c_1932, plain, (![B_516]: (B_516='#skF_8' | ~v1_xboole_0(B_516))), inference(resolution, [status(thm)], [c_1924, c_173])).
% 9.69/3.33  tff(c_1979, plain, (k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))='#skF_8'), inference(resolution, [status(thm)], [c_1916, c_1932])).
% 9.69/3.33  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.69/3.33  tff(c_125, plain, (r1_tarski('#skF_6', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_48, c_14])).
% 9.69/3.33  tff(c_1982, plain, (r1_tarski('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1979, c_125])).
% 9.69/3.33  tff(c_1935, plain, (![B_516]: (B_516='#skF_8' | ~r1_tarski(B_516, '#skF_8'))), inference(resolution, [status(thm)], [c_1924, c_8])).
% 9.69/3.33  tff(c_2010, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_1982, c_1935])).
% 9.69/3.33  tff(c_2208, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2010, c_82])).
% 9.69/3.33  tff(c_2209, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(splitLeft, [status(thm)], [c_2208])).
% 9.69/3.33  tff(c_1984, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1979, c_48])).
% 9.69/3.33  tff(c_2034, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2010, c_1984])).
% 9.69/3.33  tff(c_2696, plain, (![A_604, B_605, C_606, D_607]: (k2_partfun1(u1_struct_0(A_604), u1_struct_0(B_605), C_606, u1_struct_0(D_607))=k2_tmap_1(A_604, B_605, C_606, D_607) | ~m1_pre_topc(D_607, A_604) | ~m1_subset_1(C_606, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_604), u1_struct_0(B_605)))) | ~v1_funct_2(C_606, u1_struct_0(A_604), u1_struct_0(B_605)) | ~v1_funct_1(C_606) | ~l1_pre_topc(B_605) | ~v2_pre_topc(B_605) | v2_struct_0(B_605) | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.69/3.33  tff(c_5073, plain, (![A_722, B_723, A_724, D_725]: (k2_partfun1(u1_struct_0(A_722), u1_struct_0(B_723), A_724, u1_struct_0(D_725))=k2_tmap_1(A_722, B_723, A_724, D_725) | ~m1_pre_topc(D_725, A_722) | ~v1_funct_2(A_724, u1_struct_0(A_722), u1_struct_0(B_723)) | ~v1_funct_1(A_724) | ~l1_pre_topc(B_723) | ~v2_pre_topc(B_723) | v2_struct_0(B_723) | ~l1_pre_topc(A_722) | ~v2_pre_topc(A_722) | v2_struct_0(A_722) | ~r1_tarski(A_724, k2_zfmisc_1(u1_struct_0(A_722), u1_struct_0(B_723))))), inference(resolution, [status(thm)], [c_16, c_2696])).
% 9.69/3.33  tff(c_7122, plain, (![A_797, B_798, D_799]: (k2_partfun1(u1_struct_0(A_797), u1_struct_0(B_798), k2_zfmisc_1(u1_struct_0(A_797), u1_struct_0(B_798)), u1_struct_0(D_799))=k2_tmap_1(A_797, B_798, k2_zfmisc_1(u1_struct_0(A_797), u1_struct_0(B_798)), D_799) | ~m1_pre_topc(D_799, A_797) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_797), u1_struct_0(B_798)), u1_struct_0(A_797), u1_struct_0(B_798)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_797), u1_struct_0(B_798))) | ~l1_pre_topc(B_798) | ~v2_pre_topc(B_798) | v2_struct_0(B_798) | ~l1_pre_topc(A_797) | ~v2_pre_topc(A_797) | v2_struct_0(A_797))), inference(resolution, [status(thm)], [c_12, c_5073])).
% 9.69/3.33  tff(c_3082, plain, (![A_621, C_622, B_623, E_624, D_625]: (k3_tmap_1(A_621, B_623, C_622, D_625, E_624)=k2_partfun1(u1_struct_0(C_622), u1_struct_0(B_623), E_624, u1_struct_0(D_625)) | ~m1_pre_topc(D_625, C_622) | ~m1_subset_1(E_624, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_622), u1_struct_0(B_623)))) | ~v1_funct_2(E_624, u1_struct_0(C_622), u1_struct_0(B_623)) | ~v1_funct_1(E_624) | ~m1_pre_topc(D_625, A_621) | ~m1_pre_topc(C_622, A_621) | ~l1_pre_topc(B_623) | ~v2_pre_topc(B_623) | v2_struct_0(B_623) | ~l1_pre_topc(A_621) | ~v2_pre_topc(A_621) | v2_struct_0(A_621))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.69/3.33  tff(c_3084, plain, (![A_621, D_625, E_624]: (k3_tmap_1(A_621, '#skF_3', '#skF_2', D_625, E_624)=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_624, u1_struct_0(D_625)) | ~m1_pre_topc(D_625, '#skF_2') | ~m1_subset_1(E_624, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_624, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_624) | ~m1_pre_topc(D_625, A_621) | ~m1_pre_topc('#skF_2', A_621) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_621) | ~v2_pre_topc(A_621) | v2_struct_0(A_621))), inference(superposition, [status(thm), theory('equality')], [c_1979, c_3082])).
% 9.69/3.33  tff(c_3091, plain, (![A_621, D_625, E_624]: (k3_tmap_1(A_621, '#skF_3', '#skF_2', D_625, E_624)=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_624, u1_struct_0(D_625)) | ~m1_pre_topc(D_625, '#skF_2') | ~m1_subset_1(E_624, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_624, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_624) | ~m1_pre_topc(D_625, A_621) | ~m1_pre_topc('#skF_2', A_621) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_621) | ~v2_pre_topc(A_621) | v2_struct_0(A_621))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_3084])).
% 9.69/3.33  tff(c_3865, plain, (![A_669, D_670, E_671]: (k3_tmap_1(A_669, '#skF_3', '#skF_2', D_670, E_671)=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_671, u1_struct_0(D_670)) | ~m1_pre_topc(D_670, '#skF_2') | ~m1_subset_1(E_671, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_671, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_671) | ~m1_pre_topc(D_670, A_669) | ~m1_pre_topc('#skF_2', A_669) | ~l1_pre_topc(A_669) | ~v2_pre_topc(A_669) | v2_struct_0(A_669))), inference(negUnitSimplification, [status(thm)], [c_66, c_3091])).
% 9.69/3.33  tff(c_3867, plain, (![E_671]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_671, u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', E_671) | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(E_671, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_671, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_671) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_3865])).
% 9.69/3.33  tff(c_3872, plain, (![E_671]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_671, u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', E_671) | ~m1_subset_1(E_671, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_671, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_671) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_83, c_58, c_3867])).
% 9.69/3.33  tff(c_3873, plain, (![E_671]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), E_671, u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', E_671) | ~m1_subset_1(E_671, k1_zfmisc_1('#skF_8')) | ~v1_funct_2(E_671, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(E_671))), inference(negUnitSimplification, [status(thm)], [c_72, c_3872])).
% 9.69/3.33  tff(c_7137, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))=k2_tmap_1('#skF_2', '#skF_3', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')), '#skF_4') | ~m1_subset_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')), k1_zfmisc_1('#skF_8')) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')), u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_2') | ~v1_funct_2(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')), u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7122, c_3873])).
% 9.69/3.33  tff(c_7180, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_40, c_1979, c_85, c_1979, c_58, c_40, c_1979, c_85, c_1979, c_2034, c_1979, c_1979, c_1979, c_7137])).
% 9.69/3.33  tff(c_7181, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_7180])).
% 9.69/3.33  tff(c_2250, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2010, c_84])).
% 9.69/3.33  tff(c_2251, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_2250])).
% 9.69/3.33  tff(c_7212, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7181, c_2251])).
% 9.69/3.33  tff(c_7215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2209, c_7212])).
% 9.69/3.33  tff(c_7216, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(splitRight, [status(thm)], [c_2250])).
% 9.69/3.33  tff(c_7234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2209, c_7216])).
% 9.69/3.33  tff(c_7235, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_2208])).
% 9.69/3.33  tff(c_7262, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2010, c_84])).
% 9.69/3.33  tff(c_7263, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_7262])).
% 9.69/3.33  tff(c_7297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7235, c_7263])).
% 9.69/3.33  tff(c_7298, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(splitRight, [status(thm)], [c_7262])).
% 9.69/3.33  tff(c_1922, plain, (![B_2]: (r1_tarski('#skF_8', B_2))), inference(resolution, [status(thm)], [c_6, c_1917])).
% 9.69/3.33  tff(c_7613, plain, (![A_857, B_858, C_859, D_860]: (k2_partfun1(u1_struct_0(A_857), u1_struct_0(B_858), C_859, u1_struct_0(D_860))=k2_tmap_1(A_857, B_858, C_859, D_860) | ~m1_pre_topc(D_860, A_857) | ~m1_subset_1(C_859, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_857), u1_struct_0(B_858)))) | ~v1_funct_2(C_859, u1_struct_0(A_857), u1_struct_0(B_858)) | ~v1_funct_1(C_859) | ~l1_pre_topc(B_858) | ~v2_pre_topc(B_858) | v2_struct_0(B_858) | ~l1_pre_topc(A_857) | ~v2_pre_topc(A_857) | v2_struct_0(A_857))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.69/3.33  tff(c_9593, plain, (![A_982, B_983, A_984, D_985]: (k2_partfun1(u1_struct_0(A_982), u1_struct_0(B_983), A_984, u1_struct_0(D_985))=k2_tmap_1(A_982, B_983, A_984, D_985) | ~m1_pre_topc(D_985, A_982) | ~v1_funct_2(A_984, u1_struct_0(A_982), u1_struct_0(B_983)) | ~v1_funct_1(A_984) | ~l1_pre_topc(B_983) | ~v2_pre_topc(B_983) | v2_struct_0(B_983) | ~l1_pre_topc(A_982) | ~v2_pre_topc(A_982) | v2_struct_0(A_982) | ~r1_tarski(A_984, k2_zfmisc_1(u1_struct_0(A_982), u1_struct_0(B_983))))), inference(resolution, [status(thm)], [c_16, c_7613])).
% 9.69/3.33  tff(c_13127, plain, (![A_1076, B_1077, D_1078]: (k2_partfun1(u1_struct_0(A_1076), u1_struct_0(B_1077), k2_zfmisc_1(u1_struct_0(A_1076), u1_struct_0(B_1077)), u1_struct_0(D_1078))=k2_tmap_1(A_1076, B_1077, k2_zfmisc_1(u1_struct_0(A_1076), u1_struct_0(B_1077)), D_1078) | ~m1_pre_topc(D_1078, A_1076) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_1076), u1_struct_0(B_1077)), u1_struct_0(A_1076), u1_struct_0(B_1077)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_1076), u1_struct_0(B_1077))) | ~l1_pre_topc(B_1077) | ~v2_pre_topc(B_1077) | v2_struct_0(B_1077) | ~l1_pre_topc(A_1076) | ~v2_pre_topc(A_1076) | v2_struct_0(A_1076))), inference(resolution, [status(thm)], [c_12, c_9593])).
% 9.69/3.33  tff(c_7793, plain, (![C_878, E_880, B_879, A_877, D_881]: (k3_tmap_1(A_877, B_879, C_878, D_881, E_880)=k2_partfun1(u1_struct_0(C_878), u1_struct_0(B_879), E_880, u1_struct_0(D_881)) | ~m1_pre_topc(D_881, C_878) | ~m1_subset_1(E_880, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_878), u1_struct_0(B_879)))) | ~v1_funct_2(E_880, u1_struct_0(C_878), u1_struct_0(B_879)) | ~v1_funct_1(E_880) | ~m1_pre_topc(D_881, A_877) | ~m1_pre_topc(C_878, A_877) | ~l1_pre_topc(B_879) | ~v2_pre_topc(B_879) | v2_struct_0(B_879) | ~l1_pre_topc(A_877) | ~v2_pre_topc(A_877) | v2_struct_0(A_877))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.69/3.33  tff(c_10843, plain, (![A_1008, B_1006, C_1005, D_1004, A_1007]: (k3_tmap_1(A_1008, B_1006, C_1005, D_1004, A_1007)=k2_partfun1(u1_struct_0(C_1005), u1_struct_0(B_1006), A_1007, u1_struct_0(D_1004)) | ~m1_pre_topc(D_1004, C_1005) | ~v1_funct_2(A_1007, u1_struct_0(C_1005), u1_struct_0(B_1006)) | ~v1_funct_1(A_1007) | ~m1_pre_topc(D_1004, A_1008) | ~m1_pre_topc(C_1005, A_1008) | ~l1_pre_topc(B_1006) | ~v2_pre_topc(B_1006) | v2_struct_0(B_1006) | ~l1_pre_topc(A_1008) | ~v2_pre_topc(A_1008) | v2_struct_0(A_1008) | ~r1_tarski(A_1007, k2_zfmisc_1(u1_struct_0(C_1005), u1_struct_0(B_1006))))), inference(resolution, [status(thm)], [c_16, c_7793])).
% 9.69/3.33  tff(c_10845, plain, (![C_1005, B_1006, A_1007]: (k2_partfun1(u1_struct_0(C_1005), u1_struct_0(B_1006), A_1007, u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', B_1006, C_1005, '#skF_4', A_1007) | ~m1_pre_topc('#skF_4', C_1005) | ~v1_funct_2(A_1007, u1_struct_0(C_1005), u1_struct_0(B_1006)) | ~v1_funct_1(A_1007) | ~m1_pre_topc(C_1005, '#skF_2') | ~l1_pre_topc(B_1006) | ~v2_pre_topc(B_1006) | v2_struct_0(B_1006) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_1007, k2_zfmisc_1(u1_struct_0(C_1005), u1_struct_0(B_1006))))), inference(resolution, [status(thm)], [c_58, c_10843])).
% 9.69/3.33  tff(c_10850, plain, (![C_1005, B_1006, A_1007]: (k2_partfun1(u1_struct_0(C_1005), u1_struct_0(B_1006), A_1007, u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', B_1006, C_1005, '#skF_4', A_1007) | ~m1_pre_topc('#skF_4', C_1005) | ~v1_funct_2(A_1007, u1_struct_0(C_1005), u1_struct_0(B_1006)) | ~v1_funct_1(A_1007) | ~m1_pre_topc(C_1005, '#skF_2') | ~l1_pre_topc(B_1006) | ~v2_pre_topc(B_1006) | v2_struct_0(B_1006) | v2_struct_0('#skF_2') | ~r1_tarski(A_1007, k2_zfmisc_1(u1_struct_0(C_1005), u1_struct_0(B_1006))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_10845])).
% 9.69/3.33  tff(c_11784, plain, (![C_1041, B_1042, A_1043]: (k2_partfun1(u1_struct_0(C_1041), u1_struct_0(B_1042), A_1043, u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', B_1042, C_1041, '#skF_4', A_1043) | ~m1_pre_topc('#skF_4', C_1041) | ~v1_funct_2(A_1043, u1_struct_0(C_1041), u1_struct_0(B_1042)) | ~v1_funct_1(A_1043) | ~m1_pre_topc(C_1041, '#skF_2') | ~l1_pre_topc(B_1042) | ~v2_pre_topc(B_1042) | v2_struct_0(B_1042) | ~r1_tarski(A_1043, k2_zfmisc_1(u1_struct_0(C_1041), u1_struct_0(B_1042))))), inference(negUnitSimplification, [status(thm)], [c_72, c_10850])).
% 9.69/3.33  tff(c_11790, plain, (![A_1043]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), A_1043, u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', A_1043) | ~m1_pre_topc('#skF_4', '#skF_2') | ~v1_funct_2(A_1043, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(A_1043) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_1043, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1979, c_11784])).
% 9.69/3.33  tff(c_11811, plain, (![A_1043]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), A_1043, u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', A_1043) | ~v1_funct_2(A_1043, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(A_1043) | v2_struct_0('#skF_3') | ~r1_tarski(A_1043, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_83, c_58, c_11790])).
% 9.69/3.33  tff(c_11812, plain, (![A_1043]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), A_1043, u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', A_1043) | ~v1_funct_2(A_1043, u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(A_1043) | ~r1_tarski(A_1043, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_66, c_11811])).
% 9.69/3.33  tff(c_13138, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))=k2_tmap_1('#skF_2', '#skF_3', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')), '#skF_4') | ~v1_funct_2(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')), u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~r1_tarski(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')), '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_2') | ~v1_funct_2(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')), u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13127, c_11812])).
% 9.69/3.33  tff(c_13190, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_40, c_1979, c_85, c_1979, c_58, c_1922, c_1979, c_40, c_1979, c_85, c_1979, c_1979, c_1979, c_13138])).
% 9.69/3.33  tff(c_13191, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_13190])).
% 9.69/3.33  tff(c_7299, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_7262])).
% 9.69/3.33  tff(c_13230, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13191, c_7299])).
% 9.69/3.33  tff(c_13232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7298, c_13230])).
% 9.69/3.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.69/3.33  
% 9.69/3.33  Inference rules
% 9.69/3.33  ----------------------
% 9.69/3.33  #Ref     : 0
% 9.69/3.33  #Sup     : 3478
% 9.69/3.33  #Fact    : 0
% 9.69/3.33  #Define  : 0
% 9.69/3.33  #Split   : 57
% 9.69/3.33  #Chain   : 0
% 9.69/3.33  #Close   : 0
% 9.69/3.33  
% 9.69/3.33  Ordering : KBO
% 9.69/3.33  
% 9.69/3.33  Simplification rules
% 9.69/3.33  ----------------------
% 9.69/3.33  #Subsume      : 1910
% 9.69/3.33  #Demod        : 2489
% 9.69/3.33  #Tautology    : 618
% 9.69/3.33  #SimpNegUnit  : 158
% 9.69/3.33  #BackRed      : 63
% 9.69/3.33  
% 9.69/3.33  #Partial instantiations: 0
% 9.69/3.33  #Strategies tried      : 1
% 9.69/3.33  
% 9.69/3.33  Timing (in seconds)
% 9.69/3.33  ----------------------
% 9.69/3.34  Preprocessing        : 0.41
% 9.69/3.34  Parsing              : 0.22
% 9.69/3.34  CNF conversion       : 0.05
% 9.69/3.34  Main loop            : 2.02
% 9.69/3.34  Inferencing          : 0.62
% 9.69/3.34  Reduction            : 0.65
% 9.69/3.34  Demodulation         : 0.48
% 9.69/3.34  BG Simplification    : 0.07
% 9.69/3.34  Subsumption          : 0.57
% 9.69/3.34  Abstraction          : 0.09
% 9.69/3.34  MUC search           : 0.00
% 9.69/3.34  Cooper               : 0.00
% 9.69/3.34  Total                : 2.50
% 9.69/3.34  Index Insertion      : 0.00
% 9.69/3.34  Index Deletion       : 0.00
% 9.69/3.34  Index Matching       : 0.00
% 9.69/3.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
