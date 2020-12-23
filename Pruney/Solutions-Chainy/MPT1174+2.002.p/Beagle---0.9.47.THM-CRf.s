%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:52 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.79s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 756 expanded)
%              Number of leaves         :   36 ( 311 expanded)
%              Depth                    :   29
%              Number of atoms          :  702 (4327 expanded)
%              Number of equality atoms :  104 ( 722 expanded)
%              Maximal formula depth    :   25 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_199,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_orders_1(C,k1_orders_1(u1_struct_0(A)))
               => ! [D] :
                    ( m2_orders_2(D,A,C)
                   => ( B = k1_funct_1(C,u1_struct_0(A))
                     => k3_orders_2(A,D,B) = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_orders_2)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_174,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_orders_1(D,k1_orders_1(u1_struct_0(A)))
                 => ! [E] :
                      ( m2_orders_2(E,A,D)
                     => ( ( r2_hidden(B,E)
                          & C = k1_funct_1(D,u1_struct_0(A)) )
                       => r3_orders_2(A,C,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_orders_2)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_145,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r2_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_orders_2)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_48,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_46,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_44,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_42,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_38,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_36,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_903,plain,(
    ! [C_257,A_258,B_259] :
      ( m1_subset_1(C_257,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ m2_orders_2(C_257,A_258,B_259)
      | ~ m1_orders_1(B_259,k1_orders_1(u1_struct_0(A_258)))
      | ~ l1_orders_2(A_258)
      | ~ v5_orders_2(A_258)
      | ~ v4_orders_2(A_258)
      | ~ v3_orders_2(A_258)
      | v2_struct_0(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_905,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_903])).

tff(c_908,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_38,c_905])).

tff(c_909,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_908])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k3_orders_2(A_11,B_12,C_13),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(C_13,u1_struct_0(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_orders_2(A_11)
      | ~ v5_orders_2(A_11)
      | ~ v4_orders_2(A_11)
      | ~ v3_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    k1_funct_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_990,plain,(
    ! [A_287,D_288,B_289,E_290] :
      ( r3_orders_2(A_287,k1_funct_1(D_288,u1_struct_0(A_287)),B_289)
      | ~ r2_hidden(B_289,E_290)
      | ~ m2_orders_2(E_290,A_287,D_288)
      | ~ m1_orders_1(D_288,k1_orders_1(u1_struct_0(A_287)))
      | ~ m1_subset_1(k1_funct_1(D_288,u1_struct_0(A_287)),u1_struct_0(A_287))
      | ~ m1_subset_1(B_289,u1_struct_0(A_287))
      | ~ l1_orders_2(A_287)
      | ~ v5_orders_2(A_287)
      | ~ v4_orders_2(A_287)
      | ~ v3_orders_2(A_287)
      | v2_struct_0(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1017,plain,(
    ! [A_299,D_300,A_301,B_302] :
      ( r3_orders_2(A_299,k1_funct_1(D_300,u1_struct_0(A_299)),'#skF_1'(A_301,B_302))
      | ~ m2_orders_2(B_302,A_299,D_300)
      | ~ m1_orders_1(D_300,k1_orders_1(u1_struct_0(A_299)))
      | ~ m1_subset_1(k1_funct_1(D_300,u1_struct_0(A_299)),u1_struct_0(A_299))
      | ~ m1_subset_1('#skF_1'(A_301,B_302),u1_struct_0(A_299))
      | ~ l1_orders_2(A_299)
      | ~ v5_orders_2(A_299)
      | ~ v4_orders_2(A_299)
      | ~ v3_orders_2(A_299)
      | v2_struct_0(A_299)
      | k1_xboole_0 = B_302
      | ~ m1_subset_1(B_302,k1_zfmisc_1(A_301)) ) ),
    inference(resolution,[status(thm)],[c_2,c_990])).

tff(c_1022,plain,(
    ! [A_301,B_302] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_301,B_302))
      | ~ m2_orders_2(B_302,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_301,B_302),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = B_302
      | ~ m1_subset_1(B_302,k1_zfmisc_1(A_301)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1017])).

tff(c_1025,plain,(
    ! [A_301,B_302] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_301,B_302))
      | ~ m2_orders_2(B_302,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_301,B_302),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k1_xboole_0 = B_302
      | ~ m1_subset_1(B_302,k1_zfmisc_1(A_301)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_34,c_38,c_1022])).

tff(c_1027,plain,(
    ! [A_303,B_304] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(A_303,B_304))
      | ~ m2_orders_2(B_304,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(A_303,B_304),u1_struct_0('#skF_2'))
      | k1_xboole_0 = B_304
      | ~ m1_subset_1(B_304,k1_zfmisc_1(A_303)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1025])).

tff(c_1033,plain,(
    ! [B_305] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_305))
      | ~ m2_orders_2(B_305,'#skF_2','#skF_4')
      | k1_xboole_0 = B_305
      | ~ m1_subset_1(B_305,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1027])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_orders_2(A_18,B_19,C_20)
      | ~ r3_orders_2(A_18,B_19,C_20)
      | ~ m1_subset_1(C_20,u1_struct_0(A_18))
      | ~ m1_subset_1(B_19,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18)
      | ~ v3_orders_2(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1035,plain,(
    ! [B_305] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_305))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_305),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_305,'#skF_2','#skF_4')
      | k1_xboole_0 = B_305
      | ~ m1_subset_1(B_305,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1033,c_20])).

tff(c_1038,plain,(
    ! [B_305] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_305))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_305),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(B_305,'#skF_2','#skF_4')
      | k1_xboole_0 = B_305
      | ~ m1_subset_1(B_305,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_40,c_1035])).

tff(c_1040,plain,(
    ! [B_306] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_306))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_306),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(B_306,'#skF_2','#skF_4')
      | k1_xboole_0 = B_306
      | ~ m1_subset_1(B_306,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1038])).

tff(c_1045,plain,(
    ! [B_2] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_2))
      | ~ m2_orders_2(B_2,'#skF_2','#skF_4')
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1040])).

tff(c_943,plain,(
    ! [A_274,B_275,C_276,D_277] :
      ( r2_orders_2(A_274,B_275,C_276)
      | ~ r2_hidden(B_275,k3_orders_2(A_274,D_277,C_276))
      | ~ m1_subset_1(D_277,k1_zfmisc_1(u1_struct_0(A_274)))
      | ~ m1_subset_1(C_276,u1_struct_0(A_274))
      | ~ m1_subset_1(B_275,u1_struct_0(A_274))
      | ~ l1_orders_2(A_274)
      | ~ v5_orders_2(A_274)
      | ~ v4_orders_2(A_274)
      | ~ v3_orders_2(A_274)
      | v2_struct_0(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1087,plain,(
    ! [A_325,A_326,D_327,C_328] :
      ( r2_orders_2(A_325,'#skF_1'(A_326,k3_orders_2(A_325,D_327,C_328)),C_328)
      | ~ m1_subset_1(D_327,k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ m1_subset_1(C_328,u1_struct_0(A_325))
      | ~ m1_subset_1('#skF_1'(A_326,k3_orders_2(A_325,D_327,C_328)),u1_struct_0(A_325))
      | ~ l1_orders_2(A_325)
      | ~ v5_orders_2(A_325)
      | ~ v4_orders_2(A_325)
      | ~ v3_orders_2(A_325)
      | v2_struct_0(A_325)
      | k3_orders_2(A_325,D_327,C_328) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_325,D_327,C_328),k1_zfmisc_1(A_326)) ) ),
    inference(resolution,[status(thm)],[c_2,c_943])).

tff(c_1092,plain,(
    ! [A_329,D_330,C_331] :
      ( r2_orders_2(A_329,'#skF_1'(u1_struct_0(A_329),k3_orders_2(A_329,D_330,C_331)),C_331)
      | ~ m1_subset_1(D_330,k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ m1_subset_1(C_331,u1_struct_0(A_329))
      | ~ l1_orders_2(A_329)
      | ~ v5_orders_2(A_329)
      | ~ v4_orders_2(A_329)
      | ~ v3_orders_2(A_329)
      | v2_struct_0(A_329)
      | k3_orders_2(A_329,D_330,C_331) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_329,D_330,C_331),k1_zfmisc_1(u1_struct_0(A_329))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1087])).

tff(c_10,plain,(
    ! [A_4,B_8,C_10] :
      ( r1_orders_2(A_4,B_8,C_10)
      | ~ r2_orders_2(A_4,B_8,C_10)
      | ~ m1_subset_1(C_10,u1_struct_0(A_4))
      | ~ m1_subset_1(B_8,u1_struct_0(A_4))
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1108,plain,(
    ! [A_339,D_340,C_341] :
      ( r1_orders_2(A_339,'#skF_1'(u1_struct_0(A_339),k3_orders_2(A_339,D_340,C_341)),C_341)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_339),k3_orders_2(A_339,D_340,C_341)),u1_struct_0(A_339))
      | ~ m1_subset_1(D_340,k1_zfmisc_1(u1_struct_0(A_339)))
      | ~ m1_subset_1(C_341,u1_struct_0(A_339))
      | ~ l1_orders_2(A_339)
      | ~ v5_orders_2(A_339)
      | ~ v4_orders_2(A_339)
      | ~ v3_orders_2(A_339)
      | v2_struct_0(A_339)
      | k3_orders_2(A_339,D_340,C_341) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_339,D_340,C_341),k1_zfmisc_1(u1_struct_0(A_339))) ) ),
    inference(resolution,[status(thm)],[c_1092,c_10])).

tff(c_1113,plain,(
    ! [A_342,D_343,C_344] :
      ( r1_orders_2(A_342,'#skF_1'(u1_struct_0(A_342),k3_orders_2(A_342,D_343,C_344)),C_344)
      | ~ m1_subset_1(D_343,k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ m1_subset_1(C_344,u1_struct_0(A_342))
      | ~ l1_orders_2(A_342)
      | ~ v5_orders_2(A_342)
      | ~ v4_orders_2(A_342)
      | ~ v3_orders_2(A_342)
      | v2_struct_0(A_342)
      | k3_orders_2(A_342,D_343,C_344) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_342,D_343,C_344),k1_zfmisc_1(u1_struct_0(A_342))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1108])).

tff(c_59,plain,(
    ! [A_94,B_95,C_96] :
      ( r2_orders_2(A_94,B_95,C_96)
      | C_96 = B_95
      | ~ r1_orders_2(A_94,B_95,C_96)
      | ~ m1_subset_1(C_96,u1_struct_0(A_94))
      | ~ m1_subset_1(B_95,u1_struct_0(A_94))
      | ~ l1_orders_2(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65,plain,(
    ! [A_94,B_95,B_2] :
      ( r2_orders_2(A_94,B_95,'#skF_1'(u1_struct_0(A_94),B_2))
      | B_95 = '#skF_1'(u1_struct_0(A_94),B_2)
      | ~ r1_orders_2(A_94,B_95,'#skF_1'(u1_struct_0(A_94),B_2))
      | ~ m1_subset_1(B_95,u1_struct_0(A_94))
      | ~ l1_orders_2(A_94)
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_94))) ) ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_64,plain,(
    ! [B_95] :
      ( r2_orders_2('#skF_2',B_95,'#skF_3')
      | B_95 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_95,'#skF_3')
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_59])).

tff(c_70,plain,(
    ! [B_100] :
      ( r2_orders_2('#skF_2',B_100,'#skF_3')
      | B_100 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_100,'#skF_3')
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_64])).

tff(c_910,plain,(
    ! [B_260] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_260),'#skF_3')
      | '#skF_1'(u1_struct_0('#skF_2'),B_260) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_260),'#skF_3')
      | k1_xboole_0 = B_260
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_70])).

tff(c_22,plain,(
    ! [A_21,C_27,B_25] :
      ( ~ r2_orders_2(A_21,C_27,B_25)
      | ~ r2_orders_2(A_21,B_25,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_21))
      | ~ m1_subset_1(B_25,u1_struct_0(A_21))
      | ~ l1_orders_2(A_21)
      | ~ v5_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_912,plain,(
    ! [B_260] :
      ( ~ r2_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_260))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_260),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | '#skF_1'(u1_struct_0('#skF_2'),B_260) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_260),'#skF_3')
      | k1_xboole_0 = B_260
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_910,c_22])).

tff(c_948,plain,(
    ! [B_278] :
      ( ~ r2_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_278))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_278),u1_struct_0('#skF_2'))
      | '#skF_1'(u1_struct_0('#skF_2'),B_278) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_278),'#skF_3')
      | k1_xboole_0 = B_278
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_912])).

tff(c_954,plain,(
    ! [B_279] :
      ( ~ r2_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_279))
      | '#skF_1'(u1_struct_0('#skF_2'),B_279) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_279),'#skF_3')
      | k1_xboole_0 = B_279
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_948])).

tff(c_958,plain,(
    ! [B_2] :
      ( ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2),'#skF_3')
      | '#skF_1'(u1_struct_0('#skF_2'),B_2) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_2))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_65,c_954])).

tff(c_961,plain,(
    ! [B_2] :
      ( ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2),'#skF_3')
      | '#skF_1'(u1_struct_0('#skF_2'),B_2) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),B_2))
      | k1_xboole_0 = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_958])).

tff(c_1117,plain,(
    ! [D_343] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_343,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_343,'#skF_3')))
      | ~ m1_subset_1(D_343,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_343,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_343,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1113,c_961])).

tff(c_1120,plain,(
    ! [D_343] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_343,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_343,'#skF_3')))
      | ~ m1_subset_1(D_343,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_343,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_343,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_1117])).

tff(c_1122,plain,(
    ! [D_345] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_345,'#skF_3')) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_345,'#skF_3')))
      | ~ m1_subset_1(D_345,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',D_345,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_345,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1120])).

tff(c_1127,plain,(
    ! [D_346] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_346,'#skF_3')) = '#skF_3'
      | ~ m1_subset_1(D_346,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m2_orders_2(k3_orders_2('#skF_2',D_346,'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',D_346,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_346,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1045,c_1122])).

tff(c_1131,plain,(
    ! [B_12] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_12,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(k3_orders_2('#skF_2',B_12,'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_12,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_1127])).

tff(c_1134,plain,(
    ! [B_12] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_12,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(k3_orders_2('#skF_2',B_12,'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_12,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_1131])).

tff(c_1137,plain,(
    ! [B_354] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_354,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(k3_orders_2('#skF_2',B_354,'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_354,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_354,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1134])).

tff(c_1141,plain,(
    ! [B_12,C_13] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_12,C_13),'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_12,C_13),'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_12,C_13),'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(C_13,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_1137])).

tff(c_1151,plain,(
    ! [B_12,C_13] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_12,C_13),'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_12,C_13),'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_12,C_13),'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(C_13,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_1141])).

tff(c_1158,plain,(
    ! [B_355,C_356] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_355,C_356),'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_355,C_356),'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_355,C_356),'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(C_356,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_355,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1151])).

tff(c_1091,plain,(
    ! [A_325,D_327,C_328] :
      ( r2_orders_2(A_325,'#skF_1'(u1_struct_0(A_325),k3_orders_2(A_325,D_327,C_328)),C_328)
      | ~ m1_subset_1(D_327,k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ m1_subset_1(C_328,u1_struct_0(A_325))
      | ~ l1_orders_2(A_325)
      | ~ v5_orders_2(A_325)
      | ~ v4_orders_2(A_325)
      | ~ v3_orders_2(A_325)
      | v2_struct_0(A_325)
      | k3_orders_2(A_325,D_327,C_328) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_325,D_327,C_328),k1_zfmisc_1(u1_struct_0(A_325))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1087])).

tff(c_1172,plain,(
    ! [B_355,C_356] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_3')
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_355,C_356),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_355,C_356),'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_355,C_356),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m2_orders_2(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_355,C_356),'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_355,C_356),'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(C_356,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_355,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1158,c_1091])).

tff(c_1237,plain,(
    ! [B_355,C_356] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_3')
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_355,C_356),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_355,C_356),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m2_orders_2(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_355,C_356),'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_355,C_356),'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(C_356,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_355,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_1172])).

tff(c_1238,plain,(
    ! [B_355,C_356] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_3')
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_355,C_356),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_355,C_356),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m2_orders_2(k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_355,C_356),'#skF_3'),'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',k3_orders_2('#skF_2',B_355,C_356),'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(C_356,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_355,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1237])).

tff(c_1375,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1238])).

tff(c_1377,plain,
    ( ~ r2_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1375,c_22])).

tff(c_1385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_1375,c_1377])).

tff(c_1387,plain,(
    ~ r2_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1238])).

tff(c_922,plain,(
    ! [B_264,D_265,A_266,C_267] :
      ( r2_hidden(B_264,D_265)
      | ~ r2_hidden(B_264,k3_orders_2(A_266,D_265,C_267))
      | ~ m1_subset_1(D_265,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ m1_subset_1(C_267,u1_struct_0(A_266))
      | ~ m1_subset_1(B_264,u1_struct_0(A_266))
      | ~ l1_orders_2(A_266)
      | ~ v5_orders_2(A_266)
      | ~ v4_orders_2(A_266)
      | ~ v3_orders_2(A_266)
      | v2_struct_0(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1070,plain,(
    ! [A_318,A_319,D_320,C_321] :
      ( r2_hidden('#skF_1'(A_318,k3_orders_2(A_319,D_320,C_321)),D_320)
      | ~ m1_subset_1(D_320,k1_zfmisc_1(u1_struct_0(A_319)))
      | ~ m1_subset_1(C_321,u1_struct_0(A_319))
      | ~ m1_subset_1('#skF_1'(A_318,k3_orders_2(A_319,D_320,C_321)),u1_struct_0(A_319))
      | ~ l1_orders_2(A_319)
      | ~ v5_orders_2(A_319)
      | ~ v4_orders_2(A_319)
      | ~ v3_orders_2(A_319)
      | v2_struct_0(A_319)
      | k3_orders_2(A_319,D_320,C_321) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_319,D_320,C_321),k1_zfmisc_1(A_318)) ) ),
    inference(resolution,[status(thm)],[c_2,c_922])).

tff(c_1075,plain,(
    ! [A_322,D_323,C_324] :
      ( r2_hidden('#skF_1'(u1_struct_0(A_322),k3_orders_2(A_322,D_323,C_324)),D_323)
      | ~ m1_subset_1(D_323,k1_zfmisc_1(u1_struct_0(A_322)))
      | ~ m1_subset_1(C_324,u1_struct_0(A_322))
      | ~ l1_orders_2(A_322)
      | ~ v5_orders_2(A_322)
      | ~ v4_orders_2(A_322)
      | ~ v3_orders_2(A_322)
      | v2_struct_0(A_322)
      | k3_orders_2(A_322,D_323,C_324) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_322,D_323,C_324),k1_zfmisc_1(u1_struct_0(A_322))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1070])).

tff(c_30,plain,(
    ! [A_43,D_71,B_59,E_73] :
      ( r3_orders_2(A_43,k1_funct_1(D_71,u1_struct_0(A_43)),B_59)
      | ~ r2_hidden(B_59,E_73)
      | ~ m2_orders_2(E_73,A_43,D_71)
      | ~ m1_orders_1(D_71,k1_orders_1(u1_struct_0(A_43)))
      | ~ m1_subset_1(k1_funct_1(D_71,u1_struct_0(A_43)),u1_struct_0(A_43))
      | ~ m1_subset_1(B_59,u1_struct_0(A_43))
      | ~ l1_orders_2(A_43)
      | ~ v5_orders_2(A_43)
      | ~ v4_orders_2(A_43)
      | ~ v3_orders_2(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1447,plain,(
    ! [A_386,D_383,A_385,C_384,D_382] :
      ( r3_orders_2(A_385,k1_funct_1(D_383,u1_struct_0(A_385)),'#skF_1'(u1_struct_0(A_386),k3_orders_2(A_386,D_382,C_384)))
      | ~ m2_orders_2(D_382,A_385,D_383)
      | ~ m1_orders_1(D_383,k1_orders_1(u1_struct_0(A_385)))
      | ~ m1_subset_1(k1_funct_1(D_383,u1_struct_0(A_385)),u1_struct_0(A_385))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_386),k3_orders_2(A_386,D_382,C_384)),u1_struct_0(A_385))
      | ~ l1_orders_2(A_385)
      | ~ v5_orders_2(A_385)
      | ~ v4_orders_2(A_385)
      | ~ v3_orders_2(A_385)
      | v2_struct_0(A_385)
      | ~ m1_subset_1(D_382,k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ m1_subset_1(C_384,u1_struct_0(A_386))
      | ~ l1_orders_2(A_386)
      | ~ v5_orders_2(A_386)
      | ~ v4_orders_2(A_386)
      | ~ v3_orders_2(A_386)
      | v2_struct_0(A_386)
      | k3_orders_2(A_386,D_382,C_384) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_386,D_382,C_384),k1_zfmisc_1(u1_struct_0(A_386))) ) ),
    inference(resolution,[status(thm)],[c_1075,c_30])).

tff(c_1452,plain,(
    ! [A_386,D_382,C_384] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0(A_386),k3_orders_2(A_386,D_382,C_384)))
      | ~ m2_orders_2(D_382,'#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_386),k3_orders_2(A_386,D_382,C_384)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(D_382,k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ m1_subset_1(C_384,u1_struct_0(A_386))
      | ~ l1_orders_2(A_386)
      | ~ v5_orders_2(A_386)
      | ~ v4_orders_2(A_386)
      | ~ v3_orders_2(A_386)
      | v2_struct_0(A_386)
      | k3_orders_2(A_386,D_382,C_384) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_386,D_382,C_384),k1_zfmisc_1(u1_struct_0(A_386))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1447])).

tff(c_1455,plain,(
    ! [A_386,D_382,C_384] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0(A_386),k3_orders_2(A_386,D_382,C_384)))
      | ~ m2_orders_2(D_382,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_386),k3_orders_2(A_386,D_382,C_384)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(D_382,k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ m1_subset_1(C_384,u1_struct_0(A_386))
      | ~ l1_orders_2(A_386)
      | ~ v5_orders_2(A_386)
      | ~ v4_orders_2(A_386)
      | ~ v3_orders_2(A_386)
      | v2_struct_0(A_386)
      | k3_orders_2(A_386,D_382,C_384) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_386,D_382,C_384),k1_zfmisc_1(u1_struct_0(A_386))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_34,c_38,c_1452])).

tff(c_1457,plain,(
    ! [A_387,D_388,C_389] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0(A_387),k3_orders_2(A_387,D_388,C_389)))
      | ~ m2_orders_2(D_388,'#skF_2','#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_387),k3_orders_2(A_387,D_388,C_389)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_388,k1_zfmisc_1(u1_struct_0(A_387)))
      | ~ m1_subset_1(C_389,u1_struct_0(A_387))
      | ~ l1_orders_2(A_387)
      | ~ v5_orders_2(A_387)
      | ~ v4_orders_2(A_387)
      | ~ v3_orders_2(A_387)
      | v2_struct_0(A_387)
      | k3_orders_2(A_387,D_388,C_389) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_387,D_388,C_389),k1_zfmisc_1(u1_struct_0(A_387))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1455])).

tff(c_1461,plain,(
    ! [D_388,C_389] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_388,C_389)))
      | ~ m2_orders_2(D_388,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_388,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_389,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_388,C_389) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_388,C_389),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1457])).

tff(c_1464,plain,(
    ! [D_388,C_389] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_388,C_389)))
      | ~ m2_orders_2(D_388,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_388,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_389,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_388,C_389) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_388,C_389),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_1461])).

tff(c_1466,plain,(
    ! [D_390,C_391] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_390,C_391)))
      | ~ m2_orders_2(D_390,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_390,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_391,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_390,C_391) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_390,C_391),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1464])).

tff(c_1468,plain,(
    ! [D_390,C_391] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_390,C_391)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_390,C_391)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(D_390,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_390,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_391,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_390,C_391) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_390,C_391),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1466,c_20])).

tff(c_1471,plain,(
    ! [D_390,C_391] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_390,C_391)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_390,C_391)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(D_390,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_390,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_391,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_390,C_391) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_390,C_391),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_40,c_1468])).

tff(c_1473,plain,(
    ! [D_392,C_393] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_392,C_393)))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_392,C_393)),u1_struct_0('#skF_2'))
      | ~ m2_orders_2(D_392,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_392,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_393,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_392,C_393) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_392,C_393),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1471])).

tff(c_1478,plain,(
    ! [D_394,C_395] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_394,C_395)))
      | ~ m2_orders_2(D_394,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_394,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_395,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_394,C_395) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_394,C_395),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1473])).

tff(c_931,plain,(
    ! [A_271,B_272,B_273] :
      ( r2_orders_2(A_271,B_272,'#skF_1'(u1_struct_0(A_271),B_273))
      | B_272 = '#skF_1'(u1_struct_0(A_271),B_273)
      | ~ r1_orders_2(A_271,B_272,'#skF_1'(u1_struct_0(A_271),B_273))
      | ~ m1_subset_1(B_272,u1_struct_0(A_271))
      | ~ l1_orders_2(A_271)
      | k1_xboole_0 = B_273
      | ~ m1_subset_1(B_273,k1_zfmisc_1(u1_struct_0(A_271))) ) ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_939,plain,(
    ! [A_271,B_273,B_272] :
      ( ~ r2_orders_2(A_271,'#skF_1'(u1_struct_0(A_271),B_273),B_272)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_271),B_273),u1_struct_0(A_271))
      | ~ v5_orders_2(A_271)
      | B_272 = '#skF_1'(u1_struct_0(A_271),B_273)
      | ~ r1_orders_2(A_271,B_272,'#skF_1'(u1_struct_0(A_271),B_273))
      | ~ m1_subset_1(B_272,u1_struct_0(A_271))
      | ~ l1_orders_2(A_271)
      | k1_xboole_0 = B_273
      | ~ m1_subset_1(B_273,k1_zfmisc_1(u1_struct_0(A_271))) ) ),
    inference(resolution,[status(thm)],[c_931,c_22])).

tff(c_1428,plain,(
    ! [A_376,D_377,C_378] :
      ( ~ m1_subset_1('#skF_1'(u1_struct_0(A_376),k3_orders_2(A_376,D_377,C_378)),u1_struct_0(A_376))
      | '#skF_1'(u1_struct_0(A_376),k3_orders_2(A_376,D_377,C_378)) = C_378
      | ~ r1_orders_2(A_376,C_378,'#skF_1'(u1_struct_0(A_376),k3_orders_2(A_376,D_377,C_378)))
      | ~ m1_subset_1(D_377,k1_zfmisc_1(u1_struct_0(A_376)))
      | ~ m1_subset_1(C_378,u1_struct_0(A_376))
      | ~ l1_orders_2(A_376)
      | ~ v5_orders_2(A_376)
      | ~ v4_orders_2(A_376)
      | ~ v3_orders_2(A_376)
      | v2_struct_0(A_376)
      | k3_orders_2(A_376,D_377,C_378) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_376,D_377,C_378),k1_zfmisc_1(u1_struct_0(A_376))) ) ),
    inference(resolution,[status(thm)],[c_1092,c_939])).

tff(c_1432,plain,(
    ! [A_376,D_377,C_378] :
      ( '#skF_1'(u1_struct_0(A_376),k3_orders_2(A_376,D_377,C_378)) = C_378
      | ~ r1_orders_2(A_376,C_378,'#skF_1'(u1_struct_0(A_376),k3_orders_2(A_376,D_377,C_378)))
      | ~ m1_subset_1(D_377,k1_zfmisc_1(u1_struct_0(A_376)))
      | ~ m1_subset_1(C_378,u1_struct_0(A_376))
      | ~ l1_orders_2(A_376)
      | ~ v5_orders_2(A_376)
      | ~ v4_orders_2(A_376)
      | ~ v3_orders_2(A_376)
      | v2_struct_0(A_376)
      | k3_orders_2(A_376,D_377,C_378) = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2(A_376,D_377,C_378),k1_zfmisc_1(u1_struct_0(A_376))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1428])).

tff(c_1482,plain,(
    ! [D_394] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_394,'#skF_3')) = '#skF_3'
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(D_394,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_394,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_394,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_394,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1478,c_1432])).

tff(c_1489,plain,(
    ! [D_394] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_394,'#skF_3')) = '#skF_3'
      | v2_struct_0('#skF_2')
      | ~ m2_orders_2(D_394,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_394,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',D_394,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_394,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_48,c_46,c_44,c_42,c_1482])).

tff(c_1494,plain,(
    ! [D_396] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_396,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(D_396,'#skF_2','#skF_4')
      | ~ m1_subset_1(D_396,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | k3_orders_2('#skF_2',D_396,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_396,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1489])).

tff(c_1498,plain,(
    ! [B_12] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_12,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(B_12,'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_12,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_1494])).

tff(c_1501,plain,(
    ! [B_12] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_12,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(B_12,'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_12,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_1498])).

tff(c_1503,plain,(
    ! [B_397] :
      ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',B_397,'#skF_3')) = '#skF_3'
      | ~ m2_orders_2(B_397,'#skF_2','#skF_4')
      | k3_orders_2('#skF_2',B_397,'#skF_3') = k1_xboole_0
      | ~ m1_subset_1(B_397,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1501])).

tff(c_1510,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_909,c_1503])).

tff(c_1521,plain,
    ( '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3'
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1510])).

tff(c_1522,plain,(
    '#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_5','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1521])).

tff(c_1554,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1522,c_1091])).

tff(c_1639,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_909,c_1554])).

tff(c_1640,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_50,c_1387,c_1639])).

tff(c_1691,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_1640])).

tff(c_1694,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_909,c_40,c_1691])).

tff(c_1696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1694])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n007.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 18:03:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.86  
% 4.79/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.86  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.79/1.86  
% 4.79/1.86  %Foreground sorts:
% 4.79/1.86  
% 4.79/1.86  
% 4.79/1.86  %Background operators:
% 4.79/1.86  
% 4.79/1.86  
% 4.79/1.86  %Foreground operators:
% 4.79/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.79/1.86  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 4.79/1.86  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.79/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.79/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.79/1.86  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.79/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.79/1.86  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 4.79/1.86  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 4.79/1.86  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 4.79/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.79/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.79/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.79/1.86  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.79/1.86  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.79/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.79/1.86  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.79/1.86  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.79/1.86  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 4.79/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.79/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.79/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.79/1.86  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 4.79/1.86  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 4.79/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.79/1.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.79/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.79/1.86  
% 4.79/1.89  tff(f_199, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_orders_1(C, k1_orders_1(u1_struct_0(A))) => (![D]: (m2_orders_2(D, A, C) => ((B = k1_funct_1(C, u1_struct_0(A))) => (k3_orders_2(A, D, B) = k1_xboole_0)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_orders_2)).
% 4.79/1.89  tff(f_89, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 4.79/1.89  tff(f_69, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 4.79/1.89  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 4.79/1.89  tff(f_174, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_orders_1(D, k1_orders_1(u1_struct_0(A))) => (![E]: (m2_orders_2(E, A, D) => ((r2_hidden(B, E) & (C = k1_funct_1(D, u1_struct_0(A)))) => r3_orders_2(A, C, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_orders_2)).
% 4.79/1.89  tff(f_104, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 4.79/1.89  tff(f_145, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 4.79/1.89  tff(f_52, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 4.79/1.89  tff(f_119, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_orders_2)).
% 4.79/1.89  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.79/1.89  tff(c_48, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.79/1.89  tff(c_46, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.79/1.89  tff(c_44, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.79/1.89  tff(c_42, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.79/1.89  tff(c_38, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.79/1.89  tff(c_36, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.79/1.89  tff(c_903, plain, (![C_257, A_258, B_259]: (m1_subset_1(C_257, k1_zfmisc_1(u1_struct_0(A_258))) | ~m2_orders_2(C_257, A_258, B_259) | ~m1_orders_1(B_259, k1_orders_1(u1_struct_0(A_258))) | ~l1_orders_2(A_258) | ~v5_orders_2(A_258) | ~v4_orders_2(A_258) | ~v3_orders_2(A_258) | v2_struct_0(A_258))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.79/1.89  tff(c_905, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_903])).
% 4.79/1.89  tff(c_908, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_38, c_905])).
% 4.79/1.89  tff(c_909, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_908])).
% 4.79/1.89  tff(c_40, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.79/1.89  tff(c_12, plain, (![A_11, B_12, C_13]: (m1_subset_1(k3_orders_2(A_11, B_12, C_13), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(C_13, u1_struct_0(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_orders_2(A_11) | ~v5_orders_2(A_11) | ~v4_orders_2(A_11) | ~v3_orders_2(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.79/1.89  tff(c_32, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.79/1.89  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.79/1.89  tff(c_34, plain, (k1_funct_1('#skF_4', u1_struct_0('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_199])).
% 4.79/1.89  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.79/1.89  tff(c_990, plain, (![A_287, D_288, B_289, E_290]: (r3_orders_2(A_287, k1_funct_1(D_288, u1_struct_0(A_287)), B_289) | ~r2_hidden(B_289, E_290) | ~m2_orders_2(E_290, A_287, D_288) | ~m1_orders_1(D_288, k1_orders_1(u1_struct_0(A_287))) | ~m1_subset_1(k1_funct_1(D_288, u1_struct_0(A_287)), u1_struct_0(A_287)) | ~m1_subset_1(B_289, u1_struct_0(A_287)) | ~l1_orders_2(A_287) | ~v5_orders_2(A_287) | ~v4_orders_2(A_287) | ~v3_orders_2(A_287) | v2_struct_0(A_287))), inference(cnfTransformation, [status(thm)], [f_174])).
% 4.79/1.89  tff(c_1017, plain, (![A_299, D_300, A_301, B_302]: (r3_orders_2(A_299, k1_funct_1(D_300, u1_struct_0(A_299)), '#skF_1'(A_301, B_302)) | ~m2_orders_2(B_302, A_299, D_300) | ~m1_orders_1(D_300, k1_orders_1(u1_struct_0(A_299))) | ~m1_subset_1(k1_funct_1(D_300, u1_struct_0(A_299)), u1_struct_0(A_299)) | ~m1_subset_1('#skF_1'(A_301, B_302), u1_struct_0(A_299)) | ~l1_orders_2(A_299) | ~v5_orders_2(A_299) | ~v4_orders_2(A_299) | ~v3_orders_2(A_299) | v2_struct_0(A_299) | k1_xboole_0=B_302 | ~m1_subset_1(B_302, k1_zfmisc_1(A_301)))), inference(resolution, [status(thm)], [c_2, c_990])).
% 4.79/1.89  tff(c_1022, plain, (![A_301, B_302]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_301, B_302)) | ~m2_orders_2(B_302, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_301, B_302), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k1_xboole_0=B_302 | ~m1_subset_1(B_302, k1_zfmisc_1(A_301)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1017])).
% 4.79/1.89  tff(c_1025, plain, (![A_301, B_302]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_301, B_302)) | ~m2_orders_2(B_302, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_301, B_302), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k1_xboole_0=B_302 | ~m1_subset_1(B_302, k1_zfmisc_1(A_301)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_34, c_38, c_1022])).
% 4.79/1.89  tff(c_1027, plain, (![A_303, B_304]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(A_303, B_304)) | ~m2_orders_2(B_304, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(A_303, B_304), u1_struct_0('#skF_2')) | k1_xboole_0=B_304 | ~m1_subset_1(B_304, k1_zfmisc_1(A_303)))), inference(negUnitSimplification, [status(thm)], [c_50, c_1025])).
% 4.79/1.89  tff(c_1033, plain, (![B_305]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_305)) | ~m2_orders_2(B_305, '#skF_2', '#skF_4') | k1_xboole_0=B_305 | ~m1_subset_1(B_305, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_1027])).
% 4.79/1.89  tff(c_20, plain, (![A_18, B_19, C_20]: (r1_orders_2(A_18, B_19, C_20) | ~r3_orders_2(A_18, B_19, C_20) | ~m1_subset_1(C_20, u1_struct_0(A_18)) | ~m1_subset_1(B_19, u1_struct_0(A_18)) | ~l1_orders_2(A_18) | ~v3_orders_2(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.79/1.89  tff(c_1035, plain, (![B_305]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_305)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_305), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(B_305, '#skF_2', '#skF_4') | k1_xboole_0=B_305 | ~m1_subset_1(B_305, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_1033, c_20])).
% 4.79/1.89  tff(c_1038, plain, (![B_305]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_305)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_305), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(B_305, '#skF_2', '#skF_4') | k1_xboole_0=B_305 | ~m1_subset_1(B_305, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_40, c_1035])).
% 4.79/1.89  tff(c_1040, plain, (![B_306]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_306)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_306), u1_struct_0('#skF_2')) | ~m2_orders_2(B_306, '#skF_2', '#skF_4') | k1_xboole_0=B_306 | ~m1_subset_1(B_306, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1038])).
% 4.79/1.89  tff(c_1045, plain, (![B_2]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_2)) | ~m2_orders_2(B_2, '#skF_2', '#skF_4') | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_1040])).
% 4.79/1.89  tff(c_943, plain, (![A_274, B_275, C_276, D_277]: (r2_orders_2(A_274, B_275, C_276) | ~r2_hidden(B_275, k3_orders_2(A_274, D_277, C_276)) | ~m1_subset_1(D_277, k1_zfmisc_1(u1_struct_0(A_274))) | ~m1_subset_1(C_276, u1_struct_0(A_274)) | ~m1_subset_1(B_275, u1_struct_0(A_274)) | ~l1_orders_2(A_274) | ~v5_orders_2(A_274) | ~v4_orders_2(A_274) | ~v3_orders_2(A_274) | v2_struct_0(A_274))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.79/1.89  tff(c_1087, plain, (![A_325, A_326, D_327, C_328]: (r2_orders_2(A_325, '#skF_1'(A_326, k3_orders_2(A_325, D_327, C_328)), C_328) | ~m1_subset_1(D_327, k1_zfmisc_1(u1_struct_0(A_325))) | ~m1_subset_1(C_328, u1_struct_0(A_325)) | ~m1_subset_1('#skF_1'(A_326, k3_orders_2(A_325, D_327, C_328)), u1_struct_0(A_325)) | ~l1_orders_2(A_325) | ~v5_orders_2(A_325) | ~v4_orders_2(A_325) | ~v3_orders_2(A_325) | v2_struct_0(A_325) | k3_orders_2(A_325, D_327, C_328)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_325, D_327, C_328), k1_zfmisc_1(A_326)))), inference(resolution, [status(thm)], [c_2, c_943])).
% 4.79/1.89  tff(c_1092, plain, (![A_329, D_330, C_331]: (r2_orders_2(A_329, '#skF_1'(u1_struct_0(A_329), k3_orders_2(A_329, D_330, C_331)), C_331) | ~m1_subset_1(D_330, k1_zfmisc_1(u1_struct_0(A_329))) | ~m1_subset_1(C_331, u1_struct_0(A_329)) | ~l1_orders_2(A_329) | ~v5_orders_2(A_329) | ~v4_orders_2(A_329) | ~v3_orders_2(A_329) | v2_struct_0(A_329) | k3_orders_2(A_329, D_330, C_331)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_329, D_330, C_331), k1_zfmisc_1(u1_struct_0(A_329))))), inference(resolution, [status(thm)], [c_4, c_1087])).
% 4.79/1.89  tff(c_10, plain, (![A_4, B_8, C_10]: (r1_orders_2(A_4, B_8, C_10) | ~r2_orders_2(A_4, B_8, C_10) | ~m1_subset_1(C_10, u1_struct_0(A_4)) | ~m1_subset_1(B_8, u1_struct_0(A_4)) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.79/1.89  tff(c_1108, plain, (![A_339, D_340, C_341]: (r1_orders_2(A_339, '#skF_1'(u1_struct_0(A_339), k3_orders_2(A_339, D_340, C_341)), C_341) | ~m1_subset_1('#skF_1'(u1_struct_0(A_339), k3_orders_2(A_339, D_340, C_341)), u1_struct_0(A_339)) | ~m1_subset_1(D_340, k1_zfmisc_1(u1_struct_0(A_339))) | ~m1_subset_1(C_341, u1_struct_0(A_339)) | ~l1_orders_2(A_339) | ~v5_orders_2(A_339) | ~v4_orders_2(A_339) | ~v3_orders_2(A_339) | v2_struct_0(A_339) | k3_orders_2(A_339, D_340, C_341)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_339, D_340, C_341), k1_zfmisc_1(u1_struct_0(A_339))))), inference(resolution, [status(thm)], [c_1092, c_10])).
% 4.79/1.89  tff(c_1113, plain, (![A_342, D_343, C_344]: (r1_orders_2(A_342, '#skF_1'(u1_struct_0(A_342), k3_orders_2(A_342, D_343, C_344)), C_344) | ~m1_subset_1(D_343, k1_zfmisc_1(u1_struct_0(A_342))) | ~m1_subset_1(C_344, u1_struct_0(A_342)) | ~l1_orders_2(A_342) | ~v5_orders_2(A_342) | ~v4_orders_2(A_342) | ~v3_orders_2(A_342) | v2_struct_0(A_342) | k3_orders_2(A_342, D_343, C_344)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_342, D_343, C_344), k1_zfmisc_1(u1_struct_0(A_342))))), inference(resolution, [status(thm)], [c_4, c_1108])).
% 4.79/1.89  tff(c_59, plain, (![A_94, B_95, C_96]: (r2_orders_2(A_94, B_95, C_96) | C_96=B_95 | ~r1_orders_2(A_94, B_95, C_96) | ~m1_subset_1(C_96, u1_struct_0(A_94)) | ~m1_subset_1(B_95, u1_struct_0(A_94)) | ~l1_orders_2(A_94))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.79/1.89  tff(c_65, plain, (![A_94, B_95, B_2]: (r2_orders_2(A_94, B_95, '#skF_1'(u1_struct_0(A_94), B_2)) | B_95='#skF_1'(u1_struct_0(A_94), B_2) | ~r1_orders_2(A_94, B_95, '#skF_1'(u1_struct_0(A_94), B_2)) | ~m1_subset_1(B_95, u1_struct_0(A_94)) | ~l1_orders_2(A_94) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0(A_94))))), inference(resolution, [status(thm)], [c_4, c_59])).
% 4.79/1.89  tff(c_64, plain, (![B_95]: (r2_orders_2('#skF_2', B_95, '#skF_3') | B_95='#skF_3' | ~r1_orders_2('#skF_2', B_95, '#skF_3') | ~m1_subset_1(B_95, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_59])).
% 4.79/1.89  tff(c_70, plain, (![B_100]: (r2_orders_2('#skF_2', B_100, '#skF_3') | B_100='#skF_3' | ~r1_orders_2('#skF_2', B_100, '#skF_3') | ~m1_subset_1(B_100, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_64])).
% 4.79/1.89  tff(c_910, plain, (![B_260]: (r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_260), '#skF_3') | '#skF_1'(u1_struct_0('#skF_2'), B_260)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_260), '#skF_3') | k1_xboole_0=B_260 | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_70])).
% 4.79/1.89  tff(c_22, plain, (![A_21, C_27, B_25]: (~r2_orders_2(A_21, C_27, B_25) | ~r2_orders_2(A_21, B_25, C_27) | ~m1_subset_1(C_27, u1_struct_0(A_21)) | ~m1_subset_1(B_25, u1_struct_0(A_21)) | ~l1_orders_2(A_21) | ~v5_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.79/1.89  tff(c_912, plain, (![B_260]: (~r2_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_260)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_260), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | '#skF_1'(u1_struct_0('#skF_2'), B_260)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_260), '#skF_3') | k1_xboole_0=B_260 | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_910, c_22])).
% 4.79/1.89  tff(c_948, plain, (![B_278]: (~r2_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_278)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_278), u1_struct_0('#skF_2')) | '#skF_1'(u1_struct_0('#skF_2'), B_278)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_278), '#skF_3') | k1_xboole_0=B_278 | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_912])).
% 4.79/1.89  tff(c_954, plain, (![B_279]: (~r2_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_279)) | '#skF_1'(u1_struct_0('#skF_2'), B_279)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_279), '#skF_3') | k1_xboole_0=B_279 | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_948])).
% 4.79/1.89  tff(c_958, plain, (![B_2]: (~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2), '#skF_3') | '#skF_1'(u1_struct_0('#skF_2'), B_2)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_2)) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_65, c_954])).
% 4.79/1.89  tff(c_961, plain, (![B_2]: (~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2), '#skF_3') | '#skF_1'(u1_struct_0('#skF_2'), B_2)='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), B_2)) | k1_xboole_0=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_958])).
% 4.79/1.89  tff(c_1117, plain, (![D_343]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_343, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_343, '#skF_3'))) | ~m1_subset_1(D_343, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_343, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_343, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_1113, c_961])).
% 4.79/1.89  tff(c_1120, plain, (![D_343]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_343, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_343, '#skF_3'))) | ~m1_subset_1(D_343, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_343, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_343, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_1117])).
% 4.79/1.89  tff(c_1122, plain, (![D_345]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_345, '#skF_3'))='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_345, '#skF_3'))) | ~m1_subset_1(D_345, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', D_345, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_345, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1120])).
% 4.79/1.89  tff(c_1127, plain, (![D_346]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_346, '#skF_3'))='#skF_3' | ~m1_subset_1(D_346, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m2_orders_2(k3_orders_2('#skF_2', D_346, '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', D_346, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_346, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_1045, c_1122])).
% 4.79/1.89  tff(c_1131, plain, (![B_12]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_12, '#skF_3'))='#skF_3' | ~m2_orders_2(k3_orders_2('#skF_2', B_12, '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_12, '#skF_3')=k1_xboole_0 | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_1127])).
% 4.79/1.89  tff(c_1134, plain, (![B_12]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_12, '#skF_3'))='#skF_3' | ~m2_orders_2(k3_orders_2('#skF_2', B_12, '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_12, '#skF_3')=k1_xboole_0 | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_1131])).
% 4.79/1.89  tff(c_1137, plain, (![B_354]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_354, '#skF_3'))='#skF_3' | ~m2_orders_2(k3_orders_2('#skF_2', B_354, '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_354, '#skF_3')=k1_xboole_0 | ~m1_subset_1(B_354, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1134])).
% 4.79/1.89  tff(c_1141, plain, (![B_12, C_13]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_12, C_13), '#skF_3'))='#skF_3' | ~m2_orders_2(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_12, C_13), '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_12, C_13), '#skF_3')=k1_xboole_0 | ~m1_subset_1(C_13, u1_struct_0('#skF_2')) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_1137])).
% 4.79/1.89  tff(c_1151, plain, (![B_12, C_13]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_12, C_13), '#skF_3'))='#skF_3' | ~m2_orders_2(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_12, C_13), '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_12, C_13), '#skF_3')=k1_xboole_0 | ~m1_subset_1(C_13, u1_struct_0('#skF_2')) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_1141])).
% 4.79/1.89  tff(c_1158, plain, (![B_355, C_356]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_355, C_356), '#skF_3'))='#skF_3' | ~m2_orders_2(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_355, C_356), '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_355, C_356), '#skF_3')=k1_xboole_0 | ~m1_subset_1(C_356, u1_struct_0('#skF_2')) | ~m1_subset_1(B_355, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1151])).
% 4.79/1.89  tff(c_1091, plain, (![A_325, D_327, C_328]: (r2_orders_2(A_325, '#skF_1'(u1_struct_0(A_325), k3_orders_2(A_325, D_327, C_328)), C_328) | ~m1_subset_1(D_327, k1_zfmisc_1(u1_struct_0(A_325))) | ~m1_subset_1(C_328, u1_struct_0(A_325)) | ~l1_orders_2(A_325) | ~v5_orders_2(A_325) | ~v4_orders_2(A_325) | ~v3_orders_2(A_325) | v2_struct_0(A_325) | k3_orders_2(A_325, D_327, C_328)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_325, D_327, C_328), k1_zfmisc_1(u1_struct_0(A_325))))), inference(resolution, [status(thm)], [c_4, c_1087])).
% 4.79/1.89  tff(c_1172, plain, (![B_355, C_356]: (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1(k3_orders_2('#skF_2', B_355, C_356), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_355, C_356), '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_355, C_356), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m2_orders_2(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_355, C_356), '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_355, C_356), '#skF_3')=k1_xboole_0 | ~m1_subset_1(C_356, u1_struct_0('#skF_2')) | ~m1_subset_1(B_355, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_1158, c_1091])).
% 4.79/1.89  tff(c_1237, plain, (![B_355, C_356]: (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1(k3_orders_2('#skF_2', B_355, C_356), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | ~m1_subset_1(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_355, C_356), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m2_orders_2(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_355, C_356), '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_355, C_356), '#skF_3')=k1_xboole_0 | ~m1_subset_1(C_356, u1_struct_0('#skF_2')) | ~m1_subset_1(B_355, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_1172])).
% 4.79/1.89  tff(c_1238, plain, (![B_355, C_356]: (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1(k3_orders_2('#skF_2', B_355, C_356), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_355, C_356), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m2_orders_2(k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_355, C_356), '#skF_3'), '#skF_2', '#skF_4') | k3_orders_2('#skF_2', k3_orders_2('#skF_2', B_355, C_356), '#skF_3')=k1_xboole_0 | ~m1_subset_1(C_356, u1_struct_0('#skF_2')) | ~m1_subset_1(B_355, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1237])).
% 4.79/1.89  tff(c_1375, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_1238])).
% 4.79/1.89  tff(c_1377, plain, (~r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_1375, c_22])).
% 4.79/1.89  tff(c_1385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_1375, c_1377])).
% 4.79/1.89  tff(c_1387, plain, (~r2_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_1238])).
% 4.79/1.89  tff(c_922, plain, (![B_264, D_265, A_266, C_267]: (r2_hidden(B_264, D_265) | ~r2_hidden(B_264, k3_orders_2(A_266, D_265, C_267)) | ~m1_subset_1(D_265, k1_zfmisc_1(u1_struct_0(A_266))) | ~m1_subset_1(C_267, u1_struct_0(A_266)) | ~m1_subset_1(B_264, u1_struct_0(A_266)) | ~l1_orders_2(A_266) | ~v5_orders_2(A_266) | ~v4_orders_2(A_266) | ~v3_orders_2(A_266) | v2_struct_0(A_266))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.79/1.89  tff(c_1070, plain, (![A_318, A_319, D_320, C_321]: (r2_hidden('#skF_1'(A_318, k3_orders_2(A_319, D_320, C_321)), D_320) | ~m1_subset_1(D_320, k1_zfmisc_1(u1_struct_0(A_319))) | ~m1_subset_1(C_321, u1_struct_0(A_319)) | ~m1_subset_1('#skF_1'(A_318, k3_orders_2(A_319, D_320, C_321)), u1_struct_0(A_319)) | ~l1_orders_2(A_319) | ~v5_orders_2(A_319) | ~v4_orders_2(A_319) | ~v3_orders_2(A_319) | v2_struct_0(A_319) | k3_orders_2(A_319, D_320, C_321)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_319, D_320, C_321), k1_zfmisc_1(A_318)))), inference(resolution, [status(thm)], [c_2, c_922])).
% 4.79/1.89  tff(c_1075, plain, (![A_322, D_323, C_324]: (r2_hidden('#skF_1'(u1_struct_0(A_322), k3_orders_2(A_322, D_323, C_324)), D_323) | ~m1_subset_1(D_323, k1_zfmisc_1(u1_struct_0(A_322))) | ~m1_subset_1(C_324, u1_struct_0(A_322)) | ~l1_orders_2(A_322) | ~v5_orders_2(A_322) | ~v4_orders_2(A_322) | ~v3_orders_2(A_322) | v2_struct_0(A_322) | k3_orders_2(A_322, D_323, C_324)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_322, D_323, C_324), k1_zfmisc_1(u1_struct_0(A_322))))), inference(resolution, [status(thm)], [c_4, c_1070])).
% 4.79/1.89  tff(c_30, plain, (![A_43, D_71, B_59, E_73]: (r3_orders_2(A_43, k1_funct_1(D_71, u1_struct_0(A_43)), B_59) | ~r2_hidden(B_59, E_73) | ~m2_orders_2(E_73, A_43, D_71) | ~m1_orders_1(D_71, k1_orders_1(u1_struct_0(A_43))) | ~m1_subset_1(k1_funct_1(D_71, u1_struct_0(A_43)), u1_struct_0(A_43)) | ~m1_subset_1(B_59, u1_struct_0(A_43)) | ~l1_orders_2(A_43) | ~v5_orders_2(A_43) | ~v4_orders_2(A_43) | ~v3_orders_2(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_174])).
% 4.79/1.89  tff(c_1447, plain, (![A_386, D_383, A_385, C_384, D_382]: (r3_orders_2(A_385, k1_funct_1(D_383, u1_struct_0(A_385)), '#skF_1'(u1_struct_0(A_386), k3_orders_2(A_386, D_382, C_384))) | ~m2_orders_2(D_382, A_385, D_383) | ~m1_orders_1(D_383, k1_orders_1(u1_struct_0(A_385))) | ~m1_subset_1(k1_funct_1(D_383, u1_struct_0(A_385)), u1_struct_0(A_385)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_386), k3_orders_2(A_386, D_382, C_384)), u1_struct_0(A_385)) | ~l1_orders_2(A_385) | ~v5_orders_2(A_385) | ~v4_orders_2(A_385) | ~v3_orders_2(A_385) | v2_struct_0(A_385) | ~m1_subset_1(D_382, k1_zfmisc_1(u1_struct_0(A_386))) | ~m1_subset_1(C_384, u1_struct_0(A_386)) | ~l1_orders_2(A_386) | ~v5_orders_2(A_386) | ~v4_orders_2(A_386) | ~v3_orders_2(A_386) | v2_struct_0(A_386) | k3_orders_2(A_386, D_382, C_384)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_386, D_382, C_384), k1_zfmisc_1(u1_struct_0(A_386))))), inference(resolution, [status(thm)], [c_1075, c_30])).
% 4.79/1.89  tff(c_1452, plain, (![A_386, D_382, C_384]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0(A_386), k3_orders_2(A_386, D_382, C_384))) | ~m2_orders_2(D_382, '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0(A_386), k3_orders_2(A_386, D_382, C_384)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(D_382, k1_zfmisc_1(u1_struct_0(A_386))) | ~m1_subset_1(C_384, u1_struct_0(A_386)) | ~l1_orders_2(A_386) | ~v5_orders_2(A_386) | ~v4_orders_2(A_386) | ~v3_orders_2(A_386) | v2_struct_0(A_386) | k3_orders_2(A_386, D_382, C_384)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_386, D_382, C_384), k1_zfmisc_1(u1_struct_0(A_386))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1447])).
% 4.79/1.89  tff(c_1455, plain, (![A_386, D_382, C_384]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0(A_386), k3_orders_2(A_386, D_382, C_384))) | ~m2_orders_2(D_382, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0(A_386), k3_orders_2(A_386, D_382, C_384)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(D_382, k1_zfmisc_1(u1_struct_0(A_386))) | ~m1_subset_1(C_384, u1_struct_0(A_386)) | ~l1_orders_2(A_386) | ~v5_orders_2(A_386) | ~v4_orders_2(A_386) | ~v3_orders_2(A_386) | v2_struct_0(A_386) | k3_orders_2(A_386, D_382, C_384)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_386, D_382, C_384), k1_zfmisc_1(u1_struct_0(A_386))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_34, c_38, c_1452])).
% 4.79/1.89  tff(c_1457, plain, (![A_387, D_388, C_389]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0(A_387), k3_orders_2(A_387, D_388, C_389))) | ~m2_orders_2(D_388, '#skF_2', '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0(A_387), k3_orders_2(A_387, D_388, C_389)), u1_struct_0('#skF_2')) | ~m1_subset_1(D_388, k1_zfmisc_1(u1_struct_0(A_387))) | ~m1_subset_1(C_389, u1_struct_0(A_387)) | ~l1_orders_2(A_387) | ~v5_orders_2(A_387) | ~v4_orders_2(A_387) | ~v3_orders_2(A_387) | v2_struct_0(A_387) | k3_orders_2(A_387, D_388, C_389)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_387, D_388, C_389), k1_zfmisc_1(u1_struct_0(A_387))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1455])).
% 4.79/1.89  tff(c_1461, plain, (![D_388, C_389]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_388, C_389))) | ~m2_orders_2(D_388, '#skF_2', '#skF_4') | ~m1_subset_1(D_388, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_389, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_388, C_389)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_388, C_389), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_1457])).
% 4.79/1.89  tff(c_1464, plain, (![D_388, C_389]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_388, C_389))) | ~m2_orders_2(D_388, '#skF_2', '#skF_4') | ~m1_subset_1(D_388, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_389, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_388, C_389)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_388, C_389), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_1461])).
% 4.79/1.89  tff(c_1466, plain, (![D_390, C_391]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_390, C_391))) | ~m2_orders_2(D_390, '#skF_2', '#skF_4') | ~m1_subset_1(D_390, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_391, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_390, C_391)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_390, C_391), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1464])).
% 4.79/1.89  tff(c_1468, plain, (![D_390, C_391]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_390, C_391))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_390, C_391)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(D_390, '#skF_2', '#skF_4') | ~m1_subset_1(D_390, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_391, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_390, C_391)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_390, C_391), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_1466, c_20])).
% 4.79/1.89  tff(c_1471, plain, (![D_390, C_391]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_390, C_391))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_390, C_391)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m2_orders_2(D_390, '#skF_2', '#skF_4') | ~m1_subset_1(D_390, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_391, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_390, C_391)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_390, C_391), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_40, c_1468])).
% 4.79/1.89  tff(c_1473, plain, (![D_392, C_393]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_392, C_393))) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_392, C_393)), u1_struct_0('#skF_2')) | ~m2_orders_2(D_392, '#skF_2', '#skF_4') | ~m1_subset_1(D_392, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_393, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_392, C_393)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_392, C_393), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1471])).
% 4.79/1.89  tff(c_1478, plain, (![D_394, C_395]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_394, C_395))) | ~m2_orders_2(D_394, '#skF_2', '#skF_4') | ~m1_subset_1(D_394, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_395, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_394, C_395)=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_394, C_395), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_1473])).
% 4.79/1.89  tff(c_931, plain, (![A_271, B_272, B_273]: (r2_orders_2(A_271, B_272, '#skF_1'(u1_struct_0(A_271), B_273)) | B_272='#skF_1'(u1_struct_0(A_271), B_273) | ~r1_orders_2(A_271, B_272, '#skF_1'(u1_struct_0(A_271), B_273)) | ~m1_subset_1(B_272, u1_struct_0(A_271)) | ~l1_orders_2(A_271) | k1_xboole_0=B_273 | ~m1_subset_1(B_273, k1_zfmisc_1(u1_struct_0(A_271))))), inference(resolution, [status(thm)], [c_4, c_59])).
% 4.79/1.89  tff(c_939, plain, (![A_271, B_273, B_272]: (~r2_orders_2(A_271, '#skF_1'(u1_struct_0(A_271), B_273), B_272) | ~m1_subset_1('#skF_1'(u1_struct_0(A_271), B_273), u1_struct_0(A_271)) | ~v5_orders_2(A_271) | B_272='#skF_1'(u1_struct_0(A_271), B_273) | ~r1_orders_2(A_271, B_272, '#skF_1'(u1_struct_0(A_271), B_273)) | ~m1_subset_1(B_272, u1_struct_0(A_271)) | ~l1_orders_2(A_271) | k1_xboole_0=B_273 | ~m1_subset_1(B_273, k1_zfmisc_1(u1_struct_0(A_271))))), inference(resolution, [status(thm)], [c_931, c_22])).
% 4.79/1.89  tff(c_1428, plain, (![A_376, D_377, C_378]: (~m1_subset_1('#skF_1'(u1_struct_0(A_376), k3_orders_2(A_376, D_377, C_378)), u1_struct_0(A_376)) | '#skF_1'(u1_struct_0(A_376), k3_orders_2(A_376, D_377, C_378))=C_378 | ~r1_orders_2(A_376, C_378, '#skF_1'(u1_struct_0(A_376), k3_orders_2(A_376, D_377, C_378))) | ~m1_subset_1(D_377, k1_zfmisc_1(u1_struct_0(A_376))) | ~m1_subset_1(C_378, u1_struct_0(A_376)) | ~l1_orders_2(A_376) | ~v5_orders_2(A_376) | ~v4_orders_2(A_376) | ~v3_orders_2(A_376) | v2_struct_0(A_376) | k3_orders_2(A_376, D_377, C_378)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_376, D_377, C_378), k1_zfmisc_1(u1_struct_0(A_376))))), inference(resolution, [status(thm)], [c_1092, c_939])).
% 4.79/1.89  tff(c_1432, plain, (![A_376, D_377, C_378]: ('#skF_1'(u1_struct_0(A_376), k3_orders_2(A_376, D_377, C_378))=C_378 | ~r1_orders_2(A_376, C_378, '#skF_1'(u1_struct_0(A_376), k3_orders_2(A_376, D_377, C_378))) | ~m1_subset_1(D_377, k1_zfmisc_1(u1_struct_0(A_376))) | ~m1_subset_1(C_378, u1_struct_0(A_376)) | ~l1_orders_2(A_376) | ~v5_orders_2(A_376) | ~v4_orders_2(A_376) | ~v3_orders_2(A_376) | v2_struct_0(A_376) | k3_orders_2(A_376, D_377, C_378)=k1_xboole_0 | ~m1_subset_1(k3_orders_2(A_376, D_377, C_378), k1_zfmisc_1(u1_struct_0(A_376))))), inference(resolution, [status(thm)], [c_4, c_1428])).
% 4.79/1.89  tff(c_1482, plain, (![D_394]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_394, '#skF_3'))='#skF_3' | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m2_orders_2(D_394, '#skF_2', '#skF_4') | ~m1_subset_1(D_394, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_394, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_394, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_1478, c_1432])).
% 4.79/1.89  tff(c_1489, plain, (![D_394]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_394, '#skF_3'))='#skF_3' | v2_struct_0('#skF_2') | ~m2_orders_2(D_394, '#skF_2', '#skF_4') | ~m1_subset_1(D_394, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', D_394, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_394, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_48, c_46, c_44, c_42, c_1482])).
% 4.79/1.89  tff(c_1494, plain, (![D_396]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_396, '#skF_3'))='#skF_3' | ~m2_orders_2(D_396, '#skF_2', '#skF_4') | ~m1_subset_1(D_396, k1_zfmisc_1(u1_struct_0('#skF_2'))) | k3_orders_2('#skF_2', D_396, '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', D_396, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1489])).
% 4.79/1.89  tff(c_1498, plain, (![B_12]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_12, '#skF_3'))='#skF_3' | ~m2_orders_2(B_12, '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_12, '#skF_3')=k1_xboole_0 | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_1494])).
% 4.79/1.89  tff(c_1501, plain, (![B_12]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_12, '#skF_3'))='#skF_3' | ~m2_orders_2(B_12, '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_12, '#skF_3')=k1_xboole_0 | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_1498])).
% 4.79/1.89  tff(c_1503, plain, (![B_397]: ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', B_397, '#skF_3'))='#skF_3' | ~m2_orders_2(B_397, '#skF_2', '#skF_4') | k3_orders_2('#skF_2', B_397, '#skF_3')=k1_xboole_0 | ~m1_subset_1(B_397, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1501])).
% 4.79/1.89  tff(c_1510, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_909, c_1503])).
% 4.79/1.89  tff(c_1521, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3' | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1510])).
% 4.79/1.89  tff(c_1522, plain, ('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_32, c_1521])).
% 4.79/1.89  tff(c_1554, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1522, c_1091])).
% 4.79/1.89  tff(c_1639, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_909, c_1554])).
% 4.79/1.89  tff(c_1640, plain, (~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_50, c_1387, c_1639])).
% 4.79/1.89  tff(c_1691, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_1640])).
% 4.79/1.89  tff(c_1694, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_909, c_40, c_1691])).
% 4.79/1.89  tff(c_1696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1694])).
% 4.79/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.89  
% 4.79/1.89  Inference rules
% 4.79/1.89  ----------------------
% 4.79/1.89  #Ref     : 0
% 4.79/1.89  #Sup     : 314
% 4.79/1.89  #Fact    : 0
% 4.79/1.89  #Define  : 0
% 4.79/1.89  #Split   : 4
% 4.79/1.89  #Chain   : 0
% 4.79/1.89  #Close   : 0
% 4.79/1.89  
% 4.79/1.89  Ordering : KBO
% 4.79/1.89  
% 4.79/1.89  Simplification rules
% 4.79/1.89  ----------------------
% 4.79/1.89  #Subsume      : 103
% 4.79/1.89  #Demod        : 667
% 4.79/1.89  #Tautology    : 61
% 4.79/1.89  #SimpNegUnit  : 141
% 4.79/1.89  #BackRed      : 0
% 4.79/1.89  
% 4.79/1.89  #Partial instantiations: 0
% 4.79/1.89  #Strategies tried      : 1
% 4.79/1.89  
% 4.79/1.89  Timing (in seconds)
% 4.79/1.89  ----------------------
% 4.79/1.89  Preprocessing        : 0.33
% 4.79/1.89  Parsing              : 0.18
% 4.79/1.89  CNF conversion       : 0.03
% 4.79/1.89  Main loop            : 0.74
% 4.79/1.89  Inferencing          : 0.28
% 4.79/1.89  Reduction            : 0.24
% 4.79/1.89  Demodulation         : 0.17
% 4.79/1.89  BG Simplification    : 0.03
% 4.79/1.89  Subsumption          : 0.15
% 4.79/1.89  Abstraction          : 0.04
% 4.79/1.89  MUC search           : 0.00
% 4.79/1.89  Cooper               : 0.00
% 4.79/1.89  Total                : 1.12
% 4.79/1.89  Index Insertion      : 0.00
% 4.79/1.89  Index Deletion       : 0.00
% 4.79/1.89  Index Matching       : 0.00
% 4.79/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
